// GoGOST -- Pure Go GOST cryptographic functions library
// Copyright (C) 2015-2021 Sergey Matveev <stargrave@stargrave.org>
// Copyright (C) 2022 Pavel Krolevets <pavelkrolevets@gmail.com>
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, version 3 of the License.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

package gost3410

import (
	"crypto"
	"fmt"
	"math/big"
)

type PublicKey struct {
	C *Curve
	X *big.Int
	Y *big.Int
}

func NewPublicKey(c *Curve, raw []byte) (*PublicKey, error) {
	pointSize := c.PointSize()
	key := make([]byte, 2*pointSize)
	if len(raw) != len(key) {
		return nil, fmt.Errorf("gogost/gost3410: len(key) != %d", len(key))
	}
	for i := 0; i < len(key); i++ {
		key[i] = raw[len(raw)-i-1]
	}
	return &PublicKey{
		c,
		bytes2big(key[pointSize : 2*pointSize]),
		bytes2big(key[:pointSize]),
	}, nil
}

func (pub *PublicKey) Raw() []byte {
	pointSize := pub.C.PointSize()
	raw := append(
		pad(pub.Y.Bytes(), pointSize),
		pad(pub.X.Bytes(), pointSize)...,
	)
	reverse(raw)
	return raw
}

func (pub *PublicKey) VerifyDigest(digest, signature []byte) (bool, error) {
	pointSize := pub.C.PointSize()
	if len(signature) != 2*pointSize {
		return false, fmt.Errorf("gogost/gost3410: len(signature) != %d", 2*pointSize)
	}
	s := bytes2big(signature[:pointSize])
	r := bytes2big(signature[pointSize:])
	if r.Cmp(zero) <= 0 ||
		r.Cmp(pub.C.Q) >= 0 ||
		s.Cmp(zero) <= 0 ||
		s.Cmp(pub.C.Q) >= 0 {
		return false, nil
	}
	e := bytes2big(digest)
	e.Mod(e, pub.C.Q)
	if e.Cmp(zero) == 0 {
		e = big.NewInt(1)
	}
	v := big.NewInt(0)
	v.ModInverse(e, pub.C.Q)
	z1 := big.NewInt(0)
	z2 := big.NewInt(0)
	z1.Mul(s, v)
	z1.Mod(z1, pub.C.Q)
	z2.Mul(r, v)
	z2.Mod(z2, pub.C.Q)
	z2.Sub(pub.C.Q, z2)
	p1x, p1y, err := pub.C.Exp(z1, pub.C.X, pub.C.Y)
	if err != nil {
		return false, err
	}
	q1x, q1y, err := pub.C.Exp(z2, pub.X, pub.Y)
	if err != nil {
		return false, err
	}
	lm := big.NewInt(0)
	lm.Sub(q1x, p1x)
	if lm.Cmp(zero) < 0 {
		lm.Add(lm, pub.C.P)
	}
	lm.ModInverse(lm, pub.C.P)
	z1.Sub(q1y, p1y)
	lm.Mul(lm, z1)
	lm.Mod(lm, pub.C.P)
	lm.Mul(lm, lm)
	lm.Mod(lm, pub.C.P)
	lm.Sub(lm, p1x)
	lm.Sub(lm, q1x)
	lm.Mod(lm, pub.C.P)
	if lm.Cmp(zero) < 0 {
		lm.Add(lm, pub.C.P)
	}
	lm.Mod(lm, pub.C.Q)
	return lm.Cmp(r) == 0, nil
}

func (our *PublicKey) Equal(theirKey crypto.PublicKey) bool {
	their, ok := theirKey.(*PublicKey)
	if !ok {
		return false
	}
	return our.X.Cmp(their.X) == 0 && our.Y.Cmp(their.Y) == 0 && our.C.Equal(their.C)
}

func (pub *PublicKey) Ecrecover(digest, signature []byte) (*big.Int, *big.Int, error) {
	// var res []byte
	pointSize := pub.C.PointSize()
	if len(signature) != 2*pointSize {
		return nil, nil, fmt.Errorf("gogost/gost3410: len(signature) != %d", 2*pointSize)
	}
	r := bytes2big(signature[pointSize:])
	s := bytes2big(signature[:pointSize])

	if r.Cmp(zero) <= 0 ||
		r.Cmp(pub.C.Q) >= 0 ||
		s.Cmp(zero) <= 0 ||
		s.Cmp(pub.C.Q) >= 0 {
		return nil, nil, fmt.Errorf("error at r")
	}
	z := bytes2big(digest)
	z.Mod(z, pub.C.Q)
	if z.Cmp(zero) == 0 {
		z = big.NewInt(1)
	}
	var Rx,Ry, w, u1, u2 = new(big.Int), new(big.Int), new(big.Int), new(big.Int), new(big.Int)
	x3 := new(big.Int).Mul(r, r)
	x3.Mul(x3, r)
	aX := new(big.Int).Mul(pub.C.A, r)
	x3.Add(x3, aX)
	x3.Add(x3, pub.C.B)
	x3.Mod(x3, pub.C.P)
	y0 := new(big.Int).ModSqrt(x3, pub.C.P)
	if y0.Cmp(big.NewInt(0)) == 0 {
		return nil, nil, fmt.Errorf("error at computing y0")
	}

	y1 := new(big.Int).Sub(pub.C.P, y0)
	
	Rx.Set(r)
	Ry.Set(y0)
	
	w.ModInverse(r, pub.C.Q)
	
	u1.Mul(s, w)
	u1.Mod(u1, pub.C.Q)

	u2.Mul(z, w)
	u2.Neg(u2)
	u2.Mod(u2, pub.C.Q)

	u1Gx, u1Gy, err := pub.C.Exp(u1, pub.C.X, pub.C.Y)
	if err != nil {
		return nil, nil, fmt.Errorf("error at computing u1Gx, u1Gy")
	}
	u2Rx, u2Ry, err := pub.C.Exp(u2, Rx, Ry)
	if err != nil {
		return nil, nil, fmt.Errorf("error at computing u2Rx, u2Ry")
	}
	Qx, Qy := pub.C.Add(u1Gx, u1Gy, u2Rx, u2Ry)
	if Qx.Cmp(pub.X) == 0 && Qy.Cmp(pub.Y) == 0 {
			return Qx, Qy, nil
		} 
			
	u2Rx_, u2Ry_, err :=  pub.C.Exp(Rx, y1, u2)
	if err != nil {
		return nil, nil, fmt.Errorf("error at computing u2Rx_, u2Ry_")
	}
	Qx, Qy = pub.C.Add(u1Gx, u1Gy, u2Rx_, u2Ry_)
	if Qx.Cmp(pub.X) == 0 && Qy.Cmp(pub.Y) == 0 {
		return Qx, Qy, nil
	}
	return nil, nil, fmt.Errorf("cant recover public key")
}