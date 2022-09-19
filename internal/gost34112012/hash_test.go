// GoGOST -- Pure Go GOST cryptographic functions library
// Copyright (C) 2015-2021 Sergey Matveev <stargrave@stargrave.org>
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

package gost34112012

import (
	"bytes"
	"crypto/rand"
	"encoding"
	"hash"
	"testing"
	"testing/quick"
)

func TestHashInterface(t *testing.T) {
	h := New(64)
	var _ hash.Hash = h
	var _ encoding.BinaryMarshaler = h
	var _ encoding.BinaryUnmarshaler = h
}

func TestVectors(t *testing.T) {
	h512 := New(64)
	h256 := New(32)

	t.Run("1", func(t *testing.T) {
		m := []byte{
			0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
			0x38, 0x39, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35,
			0x36, 0x37, 0x38, 0x39, 0x30, 0x31, 0x32, 0x33,
			0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30, 0x31,
			0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39,
			0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
			0x38, 0x39, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35,
			0x36, 0x37, 0x38, 0x39, 0x30, 0x31, 0x32,
		}
		h512.Write(m)
		if bytes.Compare(h512.Sum(nil), []byte{
			0x1b, 0x54, 0xd0, 0x1a, 0x4a, 0xf5, 0xb9, 0xd5,
			0xcc, 0x3d, 0x86, 0xd6, 0x8d, 0x28, 0x54, 0x62,
			0xb1, 0x9a, 0xbc, 0x24, 0x75, 0x22, 0x2f, 0x35,
			0xc0, 0x85, 0x12, 0x2b, 0xe4, 0xba, 0x1f, 0xfa,
			0x00, 0xad, 0x30, 0xf8, 0x76, 0x7b, 0x3a, 0x82,
			0x38, 0x4c, 0x65, 0x74, 0xf0, 0x24, 0xc3, 0x11,
			0xe2, 0xa4, 0x81, 0x33, 0x2b, 0x08, 0xef, 0x7f,
			0x41, 0x79, 0x78, 0x91, 0xc1, 0x64, 0x6f, 0x48,
		}) != 0 {
			t.FailNow()
		}
		h256.Write(m)
		if bytes.Compare(h256.Sum(nil), []byte{
			0x9d, 0x15, 0x1e, 0xef, 0xd8, 0x59, 0x0b, 0x89,
			0xda, 0xa6, 0xba, 0x6c, 0xb7, 0x4a, 0xf9, 0x27,
			0x5d, 0xd0, 0x51, 0x02, 0x6b, 0xb1, 0x49, 0xa4,
			0x52, 0xfd, 0x84, 0xe5, 0xe5, 0x7b, 0x55, 0x00,
		}) != 0 {
			t.FailNow()
		}
	})

	t.Run("Се ветри", func(t *testing.T) {
		// It is CP1251-encoded "Се ветри, Стрибожи внуци, веютъ с моря
		// стрелами на храбрыя плъкы Игоревы" string
		h512.Reset()
		h256.Reset()
		m := []byte{
			0xd1, 0xe5, 0x20, 0xe2, 0xe5, 0xf2, 0xf0, 0xe8,
			0x2c, 0x20, 0xd1, 0xf2, 0xf0, 0xe8, 0xe1, 0xee,
			0xe6, 0xe8, 0x20, 0xe2, 0xed, 0xf3, 0xf6, 0xe8,
			0x2c, 0x20, 0xe2, 0xe5, 0xfe, 0xf2, 0xfa, 0x20,
			0xf1, 0x20, 0xec, 0xee, 0xf0, 0xff, 0x20, 0xf1,
			0xf2, 0xf0, 0xe5, 0xeb, 0xe0, 0xec, 0xe8, 0x20,
			0xed, 0xe0, 0x20, 0xf5, 0xf0, 0xe0, 0xe1, 0xf0,
			0xfb, 0xff, 0x20, 0xef, 0xeb, 0xfa, 0xea, 0xfb,
			0x20, 0xc8, 0xe3, 0xee, 0xf0, 0xe5, 0xe2, 0xfb,
		}
		h512.Write(m)
		if bytes.Compare(h512.Sum(nil), []byte{
			0x1e, 0x88, 0xe6, 0x22, 0x26, 0xbf, 0xca, 0x6f,
			0x99, 0x94, 0xf1, 0xf2, 0xd5, 0x15, 0x69, 0xe0,
			0xda, 0xf8, 0x47, 0x5a, 0x3b, 0x0f, 0xe6, 0x1a,
			0x53, 0x00, 0xee, 0xe4, 0x6d, 0x96, 0x13, 0x76,
			0x03, 0x5f, 0xe8, 0x35, 0x49, 0xad, 0xa2, 0xb8,
			0x62, 0x0f, 0xcd, 0x7c, 0x49, 0x6c, 0xe5, 0xb3,
			0x3f, 0x0c, 0xb9, 0xdd, 0xdc, 0x2b, 0x64, 0x60,
			0x14, 0x3b, 0x03, 0xda, 0xba, 0xc9, 0xfb, 0x28,
		}) != 0 {
			t.FailNow()
		}
		h256.Write(m)
		if bytes.Compare(h256.Sum(nil), []byte{
			0x9d, 0xd2, 0xfe, 0x4e, 0x90, 0x40, 0x9e, 0x5d,
			0xa8, 0x7f, 0x53, 0x97, 0x6d, 0x74, 0x05, 0xb0,
			0xc0, 0xca, 0xc6, 0x28, 0xfc, 0x66, 0x9a, 0x74,
			0x1d, 0x50, 0x06, 0x3c, 0x55, 0x7e, 0x8f, 0x50,
		}) != 0 {
			t.FailNow()
		}
	})

	t.Run("https://habr.com/ru/post/450024/", func(t *testing.T) {
		h256.Reset()
		m := []byte{
			0xd0, 0xcf, 0x11, 0xe0, 0xa1, 0xb1, 0x1a, 0xe1,
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x3e, 0x00, 0x03, 0x00, 0xfe, 0xff, 0x09, 0x00,
			0x06, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
			0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x00, 0x10, 0x00, 0x00, 0x24, 0x00, 0x00, 0x00,
			0x01, 0x00, 0x00, 0x00, 0xfe, 0xff, 0xff, 0xff,
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
			0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
			0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
			0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
			0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
			0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
			0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
			0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
		}
		h256.Write(m)
		if bytes.Compare(h256.Sum(nil), []byte{
			0xc7, 0x66, 0x08, 0x55, 0x40, 0xca, 0xaa, 0x89,
			0x53, 0xbf, 0xcf, 0x7a, 0x1b, 0xa2, 0x20, 0x61,
			0x9c, 0xee, 0x50, 0xd6, 0x5d, 0xc2, 0x42, 0xf8,
			0x2f, 0x23, 0xba, 0x4b, 0x18, 0x0b, 0x18, 0xe0,
		}) != 0 {
			t.FailNow()
		}
	})
}

func TestBlocksized(t *testing.T) {
	h := New(64)
	m := make([]byte, BlockSize)
	for i := 0; i < BlockSize; i++ {
		m[i] = byte(i)
	}
	h.Write(m)
	if bytes.Compare(h.Sum(nil), []byte{
		0x2a, 0xe5, 0x81, 0xf1, 0x8a, 0xe8, 0x5e, 0x35,
		0x96, 0xc9, 0x36, 0xac, 0xbe, 0xf9, 0x10, 0xf2,
		0xed, 0x70, 0xdc, 0xf9, 0x1e, 0xd5, 0xd2, 0x4b,
		0x39, 0xa5, 0xaf, 0x65, 0x7b, 0xf8, 0x23, 0x2a,
		0x30, 0x3d, 0x68, 0x60, 0x56, 0xc8, 0xc0, 0x0b,
		0xf3, 0x0d, 0x42, 0xe1, 0x6c, 0xe2, 0x55, 0x42,
		0x6f, 0xa8, 0xa1, 0x55, 0xdc, 0xb3, 0xeb, 0x82,
		0x2d, 0x92, 0x58, 0x08, 0xf7, 0xc7, 0xe3, 0x45,
	}) != 0 {
		t.FailNow()
	}
}

func TestBehaviour(t *testing.T) {
	h := New(64)
	// Sum does not change the state
	hsh1 := h.Sum(nil)
	if bytes.Compare(h.Sum(nil), hsh1) != 0 {
		t.FailNow()
	}
	// No data equals to no state changing
	h.Write([]byte{})
	if bytes.Compare(h.Sum(nil), hsh1) != 0 {
		t.FailNow()
	}
	// Just to be sure
	h.Write([]byte{})
	if bytes.Compare(h.Sum(nil), hsh1) != 0 {
		t.FailNow()
	}
}

func TestRandom(t *testing.T) {
	h := New(64)
	f := func(data []byte) bool {
		h.Reset()
		h.Write(data)
		d1 := h.Sum(nil)
		h1Raw, err := h.MarshalBinary()
		if err != nil {
			return false
		}
		h.Reset()
		for _, c := range data {
			h.Write([]byte{c})
		}
		d2 := h.Sum(nil)
		if bytes.Compare(d1, d2) != 0 {
			return false
		}
		h2Raw, err := h.MarshalBinary()
		if err != nil {
			return false
		}
		if bytes.Compare(h1Raw, h2Raw) != 0 {
			return false
		}
		hNew := New(64)
		if err = hNew.UnmarshalBinary(h1Raw); err != nil {
			return false
		}
		return bytes.Compare(hNew.Sum(nil), d1) == 0
	}
	if err := quick.Check(f, nil); err != nil {
		t.Error(err)
	}
}

func BenchmarkHash(b *testing.B) {
	h := New(64)
	src := make([]byte, BlockSize+1)
	rand.Read(src)
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		h.Write(src)
		h.Sum(nil)
	}
}
