/* These algorithms are a snapshot taken 2010-10-29 from my SHA3-JS github
 * repository, http://github.com/drostie/sha3-js . They have been modified to
 * take byte arrays as inputs so that they can work with d.o.transcode, which
 * forms the initial conversion step. 
 */

function intify(mode, array, context) {
	var i, out;
	out = [];
	if (array.length % 4 !== 0) {
		throw new Error(
			"intify() error in context '" + context + 
			"': array length " + array.length + " not divisible by four."
		);
	}
	switch (mode) {
	case 'be':
		for (i = 0; i < array.length; i += 4) {
			out.push((array[i] << 24) | (array[i + 1] << 16) | (array[i + 2] << 8) | array[i + 3]);
		}
		return out;
	case 'le':
		for (i = 0; i < array.length; i += 4) {
			out.push((array[i + 3] << 24) | (array[i + 2] << 16) | (array[i + 1] << 8) | array[i]);
		}
		return out;
	default:
		throw new Error("intify() error: no such mode '" + mode + "'.");
	}
}

var sha3_algos = {
	blake32: (function () {
		var iv, g, r, block, constants, sigma, circ, state, message, output, two32;
		two32 = 4 * (1 << 30);
		iv = [
			0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
			0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
		];
		constants = [
			0x243F6A88, 0x85A308D3, 0x13198A2E, 0x03707344, 
			0xA4093822, 0x299F31D0, 0x082EFA98, 0xEC4E6C89, 
			0x452821E6, 0x38D01377, 0xBE5466CF, 0x34E90C6C, 
			0xC0AC29B7, 0xC97C50DD, 0x3F84D5B5, 0xB5470917
		];
		output = function (i) {
			if (i < 0) {
				i += two32;
			}
			return ("00000000" + i.toString(16)).slice(-8);
		};
		/* The spec calls for 2*i and 2 * i + 1 to be passed into the g function 
		* simultaneously. This implementation splits this even-and-odd distinction
		* in the source code itself: sigma.u[r][i] is the even coefficient and
		* sigma.v[r][i] is the odd one. 
		*/
		sigma = {
			u: [
				[0, 2, 4, 6, 8, 10, 12, 14],   [14, 4, 9, 13, 1, 0, 11, 5], 
				[11, 12, 5, 15, 10, 3, 7, 9],  [7, 3, 13, 11, 2, 5, 4, 15], 
				[9, 5, 2, 10, 14, 11, 6, 3],   [2, 6, 0, 8, 4, 7, 15, 1], 
				[12, 1, 14, 4, 0, 6, 9, 8],    [13, 7, 12, 3, 5, 15, 8, 2], 
				[6, 14, 11, 0, 12, 13, 1, 10], [10, 8, 7, 1, 15, 9, 3, 13]
			], 
			v: [
				[1, 3, 5, 7, 9, 11, 13, 15],  [10, 8, 15, 6, 12, 2, 7, 3], 
				[8, 0, 2, 13, 14, 6, 1, 4],   [9, 1, 12, 14, 6, 10, 0, 8], 
				[0, 7, 4, 15, 1, 12, 8, 13],  [12, 10, 11, 3, 13, 5, 14, 9], 
				[5, 15, 13, 10, 7, 3, 2, 11], [11, 14, 1, 9, 0, 4, 6, 10], 
				[15, 9, 3, 8, 2, 7, 4, 5],    [2, 4, 6, 5, 11, 14, 12, 0]
			]
		};
		circ = function (a, b, n) {
			var s = state[a] ^ state[b];
			state[a] = (s >>> n) | (s << (32 - n));
		};
		g = function (i, a, b, c, d) {
			var u = block + sigma.u[r][i], v = block + sigma.v[r][i];
			state[a] += state[b] + (message[u] ^ constants[v % 16]);
			circ(d, a, 16);
			state[c] += state[d];
			circ(b, c, 12);
			state[a] += state[b] + (message[v] ^ constants[u % 16]);
			circ(d, a, 8);
			state[c] += state[d];
			circ(b, c, 7);
		};
		return function (msg, salt) {
			if (! (salt instanceof Array && salt.length === 4)) {
				salt = [0, 0, 0, 0];
			}
			var pad, chain, len, L, last_L, last, total, i; 
			chain = iv.slice(0);
			pad = constants.slice(0, 8);
			for (r = 0; r < 4; r += 1) {
				pad[r] ^= salt[r];
			}
			// pre-padding bit length of the string.
			len = msg.length * 8;
			last_L = (len % 512 > 446 || len % 512 === 0) ? 0 : len;
			// padding step: append a 1, then a bunch of 0's until we're at 447 bits,
			// then another 1 (note: 448/16 = 28), then len as a 64-bit integer.
			if (len % 512 === 440) {
				msg.push(0x81);
			} else {
				msg.push(0x80);
				while (msg.length % 64 !== 55) {
					msg.push(0);
				}
				msg.push(1);
			}
			message = intify('be', msg, 'blake32');
			message.push(0);
			message.push(len);
			last = message.length - 16;
			total = 0;
			for (block = 0; block < message.length; block += 16) {
				total += 512;
				L = (block === last) ? last_L : Math.min(len, total);
				state = chain.concat(pad);
				state[12] ^= L;
				state[13] ^= L;
				for (r = 0; r < 10; r += 1) {
					g(0, 0, 4,  8, 12);
					g(1, 1, 5,  9, 13);
					g(2, 2, 6, 10, 14);
					g(3, 3, 7, 11, 15);
					g(4, 0, 5, 10, 15);
					g(5, 1, 6, 11, 12);
					g(6, 2, 7,  8, 13);
					g(7, 3, 4,  9, 14);
				}
				for (i = 0; i < 8; i += 1) {
					chain[i] ^= salt[i % 4] ^ state[i] ^ state[i + 8];
				}
			}
			return chain.map(output).join("");
		};
	}()),
	bmw: (function () {
		var hex, output_fn, compress, H, iv, final, u;
		// output formatting function, giving the little-endian hex display of a number.
		hex = function (n) {
			return ("00" + n.toString(16)).slice(-2);
		};
		output_fn = function (n) {
			return hex(n & 255) + hex(n >>> 8) + hex(n >>> 16) + hex(n >>> 24);
		};
		// initial constants.
		iv = [0x40414243];
		final = [0xaaaaaaa0];
		for (u = 0; u < 15; u += 1) {
			final.push(final[u] + 1);
			iv.push(iv[u] + 0x04040404);
		}
		// This compress function is sufficiently complicated that I've decided to give 
		// it its own dedicated constructor function and variable-space. 
		compress = (function () {
			var i, rot, fold, s, Q, expansion_constants_sign, expansion_constants_num, expand1_fns, expand2_fns;
			rot = function (x, n) {
				return (x << n) + (x >>> (32 - n));
			};
			// y and z are generic templates for s and the expansion functions.
			function y(n) {
				var m = 32 - n;
				return function (x) {
					return (x << n) ^ (x >>> m);
				};
			}
			function z(i, j, m, p) {
				var n = 32 - m,
					q = 32 - p;
				return (j === undefined) ?
				function (x) {
					return x ^ (x >>> i);
				} : function (x) {
					return (x >>> i) ^ (x << j) ^ (x << m) ^ (x >>> n) ^ (x << p) ^ (x >>> q);
				};
			}
			// I also define an identity function for the sake of exp2.
			function I(n) { 
				return n;
			}
			// The BMW spec defines five s-functions.
			s = [z(1, 3, 4, 19), z(1, 2, 8, 23), z(2, 1, 12, 25), z(2, 2, 15, 29), z(1), z(2)];
			
			// There are two sets of expansions, expand1() and expand2(), defined in the spec.
			// Since they both have a similar operation, we give them here a similar form, 
			// defining just the 16 functions that each uses on its arguments.
			
			// expand1_fns = [s1, s2, s3, s0, s1, s2, s3, s0, ...].
			expand1_fns = [];
			for (i = 0; i < 16; i += 1) {
				expand1_fns[i] = s[(i + 1) % 4];
			}
			expand2_fns = [I, y(3), I, y(7), I, y(13), I, y(16), I, y(19), I, y(23), I, y(27), s[4], s[5]];
			
			// u and v are templates for the fold[] functions. 
			function u(m, n, reverse) {
				return function (x, y) {
					return reverse ? (y >>> n) ^ (x << m) : (x >>> m) ^ (y << n);
				};
			}
			function v(m, reverse) {
				return function (x) {
					return reverse ? (x << m) : (x >>> m);
				};
			}
			// this array takes care of the part of the "folding" step that depends on i.
			fold = [
				u(5, 5, 1), u(7, 8), u(5, 5), u(1, 5), 
				u(3, 0), u(6, 6, 1), u(4, 6), u(11, 2), 
				v(8, 1), v(6), v(6, 1), v(4, 1), 
				v(3), v(4), v(7), v(2)
			];
			
			// the initial quad-expansion is actually very regular, except that it has 
			// a set of random minus signs thrown in.
			expansion_constants_sign = "+-+++,+-++-,++-++,+-++-,+--++,+-+-+,-+--+,--+--,+-+--,++-+-,+---+,---++,++--+,+++++,+-+--,---++"
				.split(",");
			expansion_constants_num = [5, 7, 10, 13, 14];
			return function (m) {
				var lo, hi, i, j, k, a, b;
				Q = [];
				for (i = 0; i < 16; i += 1) {
					a = 0; 
					for (j = 0; j < 5; j += 1) {
						k = (i + expansion_constants_num[j]) % 16;
						b = H[k] ^ m[k];
						a += expansion_constants_sign[i].charAt(j) === "+" ? b : -b;
					}
					Q[i] = H[(i + 1) % 16] + s[i % 5](a);
				}
				for (i = 16; i < 32; i += 1) {
					j = i - 16;
					a = (j + 3) % 16;
					b = (j + 10) % 16;
					Q[i] = H[(j + 7) % 16] ^ (i * 0x05555555 +
						rot(m[j], 1 + j) + 
						rot(m[a], 1 + a) -
						rot(m[b], 1 + b));
					for (k = 0; k < 16; k += 1) {
						Q[i] += (i < 18 ? expand1_fns : expand2_fns)[k](Q[j + k]);
					}
				}
				lo = hi = 0;
				for (i = 16; i < 24; i += 1) {
					lo ^= Q[i];
					hi ^= Q[i + 8];
				}
				hi ^= lo;
				
				for (i = 0; i < 16; i += 1) {
					H[i] = (i < 8) ? 
						(lo ^ Q[i] ^ Q[i + 24]) + (m[i] ^ fold[i](hi, Q[i + 16])) : 
						(hi ^ m[i] ^ Q[i + 16]) + (Q[i] ^ fold[i](lo) ^ Q[16 + (i - 1) % 8]) + 
							rot(H[(i - 4) % 8], i + 1);
				}
			};
		}()); // construct compress();
		
		// The bmw() function.
		return function (msg) {
			var len, i, data, temp;
			len = 8 * msg.length;
			msg.push(0x80);
			while (msg.length % 64 !== 56) {
				msg.push(0);
			}
			data = intify('le', msg, 'bmw');
			data.push(len);
			data.push(0);
			H = iv.slice(0);
			for (i = 0; i < data.length; i += 16) {
				compress(data.slice(i, i + 16));
			}
			temp = H;
			H = final.slice(0);
			compress(temp);
			return H.slice(8, 16).map(output_fn).join("");
		};
	}()),
	cubehash: (function () {
		var state, round, input, initial_state, out_length, tmp, i, j, r, plus_rotate, swap_xor_swap, hex, output_fn;
		out_length = 256;
		state = [
			out_length / 8, 32, 16, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0
		];
		
		plus_rotate = function (r, s) {
			for (i = 0; i < 16; i += 1) {
				state[16 + i] += state[i];
				state[i] = (state[i] << r) ^ (state[i] >>> s);
			}
		};

			// swap, xor, and swap steps.
		swap_xor_swap = function (mask1, mask2) {
			for (i = 0; i < 16; i += 1) {
				if (i & mask1) {
					j = i ^ mask1;
					tmp = state[i] ^ state[j + 16];
					state[i] = state[j] ^ state[i + 16];
					state[j] = tmp;
				}
			}
			for (i = 16; i < 32; i += 1) {
				if (i & mask2) {
					j = i ^ mask2;
					tmp = state[i];
					state[i] = state[j];
					state[j] = tmp;
				}
			}
		};
		round = function (n) {
			n *= 16;
			for (r = 0; r < n; r += 1) {
				plus_rotate(7, 25);
				swap_xor_swap(8, 2);
				plus_rotate(11, 21);
				swap_xor_swap(4, 1);
			}
		};
		// we initialize the state and save it.
		round(10);
		initial_state = state.slice(0);
		
		// output formatting function, giving the little-endian hex display of a number.
		hex = function (n) {
			return ("00" + n.toString(16)).slice(-2);
		};
		output_fn = function (n) {
			return hex(n & 255) + hex(n >>> 8) + hex(n >>> 16) + hex(n >>> 24);
		};
		
		return function (str) {
			var block, i;
			state = initial_state.slice(0);
			str.push(0x80);
			while (str.length % 32 > 0) {
				str.push(0);
			}
			input = intify('le', str, 'cubehash');
			for (block = 0; block < input.length; block += 8) {
				for (i = 0; i < 8; i += 1) {
					state[i] ^= input[block + i];
				}
				round(1);
			}
			state[31] ^= 1;
			round(10);
			return state.map(output_fn).join("").substring(0, out_length / 4);
		};
	}()),
	halfskein: (function () {
		var even, odd, charcode, zero, pad, rot, ubi, initial, state, mix, hex, output_fn, subkey_inject;
		//permutation constants
		even = [0, 2, 4, 6, 2, 4, 6, 0, 4, 6, 0, 2, 6, 0, 2, 4];
		odd = [1, 3, 5, 7, 1, 7, 5, 3, 1, 3, 5, 7, 1, 7, 5, 3];
		charcode = String.fromCharCode;
		zero = charcode(0);
		// padding string: sixteen zero-characters, modified here to 32 bytes
		pad = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0]
		pad = pad.concat(pad);
		
		// rotation constants: f([3, 14, 15, 92, 65, 35...]).
		rot = [
			[5, 16, 17, 10, 11, 9, 7, 25, 6, 12, 20, 28, 17, 12, 6, 25], 
			[24, 2, 2, 21, 17, 15, 13, 11, 21, 12, 4, 22, 15, 23, 18, 5]
		];
		subkey_inject = function (key, tweak, round) {
			for (var i = 0; i < 8; i += 1) {
				state[i] += key[(round + i) % 9];
			}
			state[5] += tweak[round % 5];
			state[6] += tweak[(round + 1) % 5];
			state[7] += round;
		};
		mix = function (r) {
			// input: one of the two arrays of round constants.
			var a, b, i;
			for (i = 0; i < 16; i += 1) {
				a = even[i];
				b = odd[i];
				state[a] += state[b];
				state[b] = state[a] ^ (state[b] << r[i] | state[b] >>> 32 - r[i]);
			}
		};
		
		// UBI calls on the chaining state c have a type number T (0-63), and some
		// data string D, while c is itself used as a Threefish32 key schedule.
		ubi = function (type, message) {
			var key, data, i, j, block, round, first, last, tweak, original_length;
			// the message is padded with zeroes and turned into 32-bit ints.
			// first we store the original length
			original_length = message.length;
			if (original_length % 32) {
				message = message.concat(pad.slice(original_length % 32));
			} else if (original_length === 0) {
				message = pad;
			}
			// then we construct the data array.
			data = intify('le', message, 'halfskein');
			// we want a pointer last block, and tweak flags for first and type.
			first = 1 << 30;
			type <<= 24;
			last = data.length - 8;
			for (block = 0; block <= last; block += 8) {
				// tweak field. we're processing ints (block -> block + 8),
				// which each take up four bytes. On the last block we don't count
				// the padding 0's and we raise a "last" flag.
				tweak = (block === last) ? 
					[original_length, 0, 0, first + type + (1 << 31)] :
					[4 * block + 32, 0, 0, first + type];
				// extended tweak field.
				tweak[4] = tweak[0] ^ tweak[3];
				
				// the key for threefish encryption is extended from the chaining state
				// with one extra value.
				key = state;
				key[8] = 0x55555555;
				for (i = 0; i < 8; i += 1) {
					key[8] ^= key[i];
				}
				// and the state now gets the plaintext for this UBI iteration.
				state = data.slice(block, block + 8);
				
				// Each "mix" is four "rounds" of threefish32, so the 18 here 
				// is essentially 4*18 = 72 in the spec.
				for (round = 0; round < 18; round += 1) {
					subkey_inject(key, tweak, round);
					mix(rot[round % 2]);
				}
				// there is then one final subkey addition in Threefish32:
				subkey_inject(key, tweak, round);
				// now we pass on to Matyas-Meyer-Oseas, XORing the source data
				// into the current state vector.
				for (i = 0; i < 8; i += 1) {
					state[i] ^= data[block + i];
				}
				first = 0;
			}
		};
		// output formatting function, giving the little-endian hex display of a number.
		hex = function (n) {
			return ("00" + n.toString(16)).slice(-2);
		};
		output_fn = function (n) {
			return hex(n & 255) + hex(n >>> 8) + hex(n >>> 16) + hex(n >>> 24);
		};
		state = [0, 0, 0, 0, 0, 0, 0, 0];
		
		// below, the config block should be ASCII bytes for "SHA3", but it has 
		// intentionally been left as ASCII bytes for "hSkn" instead.
		
		// different options for configuration:
		// ubi(0, "key string")
		ubi(4, [0x68, 0x53, 0x6b, 0x6e, 1, 0, 0, 0, 0, 1].concat(pad.slice(10)))
		// ubi(8, "personalization as UTF-16, against the standard.");
		// ubi(12, "public key string, if such exists.");
		// ubi(16, "key identifier");
		// ubi(20, "nonce input");
		initial = state;
		return function (m) {
			state = initial.slice(0);
			ubi(48, m);
			ubi(63, [0,0,0,0, 0,0,0,0]);
			return state.map(output_fn).join("");
		};
	}()),
	keccak32: (function () {
		var permute, RC, r, circ, hex, output_fn;
		permute = [0, 10, 20, 5, 15, 16, 1, 11, 21, 6, 7, 17, 2, 12, 22, 23, 8, 18, 3, 13, 14, 24, 9, 19, 4];
		RC = "1,8082,808a,80008000,808b,80000001,80008081,8009,8a,88,80008009,8000000a,8000808b,8b,8089,8003,8002,80,800a,8000000a,80008081,8080"
			.split(",").map(function (i) { 
				return parseInt(i, 16); 
			});
		r = [0, 1, 30, 28, 27, 4, 12, 6, 23, 20, 3, 10, 11, 25, 7, 9, 13, 15, 21, 8, 18, 2, 29, 24, 14];
		circ = function (s, n) {
			return (s << n) | (s >>> (32 - n));
		};
		hex = function (n) {
			return ("00" + n.toString(16)).slice(-2);
		};
		output_fn = function (n) {
			return hex(n & 255) + hex(n >>> 8) + hex(n >>> 16) + hex(n >>> 24);
		};
		return function (array) {
			var i, b, k, x, y, C, D, round, next, state, m;
			state = [];
			for (i = 0; i < 25; i += 1) {
				state[i] = 0;
			}
			C = [];
			D = [];
			next = [];
			array = array.concat([1, 0, 0x20, 1]);
			while (array.length % 32 !== 0) {
				array.push(0);
			}
			m = intify('le', array, 'keccak32');
			for (b = 0; b < m.length; b += 8) {
				for (k = 0; k < 8; k += 1) {
					state[k] ^= m[b + k];
				}
				for (round = 0; round < 22; round += 1) {
					for (x = 0; x < 5; x += 1) {
						C[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20]; 
					}
					for (x = 0; x < 5; x += 1) {
						D[x] = C[(x + 4) % 5] ^ circ(C[(x + 1) % 5], 1);
					}
					for (i = 0; i < 25; i += 1) {
						next[permute[i]] = circ(state[i] ^ D[i % 5], r[i]);
					}
					for (x = 0; x < 5; x += 1) {
						for (y = 0; y < 25; y += 5) {
							state[y + x] = next[y + x] ^ ((~ next[y + (x + 1) % 5]) & (next[y + (x + 2) % 5]));
						}
					}
					state[0] ^= RC[round];
				}
			}
			return state.slice(0, 8).map(output_fn).join("");
		};
	}()),
	keccak: (function () {
		var state, State, L, permute, zeros, RC, r, keccak_f;
		L = function (lo, hi) {
			this.lo = lo ? lo : 0;
			this.hi = hi ? hi : 0;
		};
		L.clone = function (a) {
			return new L(a.lo, a.hi);
		};
		L.prototype = {
			xor: function (that) {
				this.lo ^= that.lo;
				this.hi ^= that.hi;
				return this;
			},
			not: function () {
				return new L(~this.lo, ~this.hi);
			},
			and: function (that) {
				this.lo &= that.lo;
				this.hi &= that.hi;
				return this;
			},
			circ: function (n) {
				var tmp, m;
				if (n >= 32) {
					tmp = this.lo;
					this.lo = this.hi;
					this.hi = tmp;
					n -= 32;
				}
				if (n === 0) {
					return this;
				}
				m = 32 - n;
				tmp = (this.hi << n) + (this.lo >>> m);
				this.lo = (this.lo << n) + (this.hi >>> m);
				this.hi = tmp;
				return this;
			},
			toString: (function () {
				var hex, o;
				hex = function (n) {
					return ("00" + n.toString(16)).slice(-2);
				};
				o = function (n) {
					return hex(n & 255) + hex(n >>> 8) + hex(n >>> 16) + hex(n >>> 24);
				};
				return function () {
					return o(this.lo) + o(this.hi);
				};
			}())
		};
		zeros = function (k) {
			var i, z = [];
			for (i = 0; i < k; i += 1) {
				z[i] = new L();
			}
			return z;
		};
		State = function (s) {
			var fn = function (x, y) {
				return fn.array[(x % 5) + 5 * (y % 5)];
			};
			fn.array = s ? s : zeros(25);
			fn.clone = function () {
				return new State(fn.array.map(L.clone));
			};
			return fn;
		};
			
		permute = [0, 10, 20, 5, 15, 16, 1, 11, 21, 6, 7, 17, 2, 12, 22, 23, 8, 18, 3, 13, 14, 24, 9, 19, 4];
		RC = "0,1;0,8082;z,808A;z,yy;0,808B;0,y0001;z,y8081;z,8009;0,8A;0,88;0,y8009;0,y000A;0,y808B;z,8B;z,8089;z,8003;z,8002;z,80;0,800A;z,y000A;z,y8081;z,8080;0,y0001;z,y8008"
			.replace(/z/g, "80000000").replace(/y/g, "8000").split(";").map(function (str) {
				var k = str.split(",");
				return new L(parseInt(k[1], 16), parseInt(k[0], 16));
			});
		r = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14];
		keccak_f = function () {
			var x, y, i, b, C, D, round, last;
			for (round = 0; round < 24; round += 1) {
				// THETA STEP
				C = zeros(5);
				for (x = 0; x < 5; x += 1) {
					for (y = 0; y < 5; y += 1) {
						C[x].xor(state(x, y));
					}
				}
				// Extra logic needed because L() objects are dynamic.
				// D[x] = C[x + 1]
				D = C.map(L.clone);
				D = D.concat(D.splice(0, 1));
				// D[x] = C[x - 1] xor rot(C[x+1], 1)
				for (x = 0; x < 5; x += 1) {
					D[x].circ(1).xor(C[(x + 4) % 5]);
				}
				for (x = 0; x < 5; x += 1) {
					for (y = 0; y < 5; y += 1) {
						state(x, y).xor(D[x]);
					}
				}
				// RHO STEP
				for (x = 0; x < 5; x += 1) {
					for (y = 0; y < 5; y += 1) {
						state(x, y).circ(r[5 * y + x]);
					}
				}
				// PI STEP
				last = state.array.slice(0);
				for (i = 0; i < 25; i += 1) {
					state.array[permute[i]] = last[i];
				}
				
				// CHI STEP
				b = state.clone();
				for (x = 0; x < 5; x += 1) {
					for (y = 0; y < 5; y += 1) {
						state(x, y).xor(b(x + 1, y).not().and(b(x + 2, y)));
					}
				}
				// IOTA STEP
				state(0, 0).xor(RC[round]);
			}
		};
		return function (array) {
			state = new State();
			array = array.concat([1, 0x20, 0x88, 1]);
			while (array.length % 136 !== 0) {
				array.push(0);
			}
			var b, k, m;
			m = intify('le', array, 'keccak');
			for (b = 0; b < m.length; b += 34) {
				for (k = 0; k < 34; k += 2) {
					state.array[k / 2].xor(new L(m[b + k], m[b + k + 1]));
				}
				keccak_f();
			}
			return state.array.slice(0, 4).join("");
		};
	}()),
	shabal: (function () {
		var A, B, C, M, circ, shabal_f, ivA, ivB, ivC, z, hex, output_fn;
		circ = function (x, n) {
			return (x << n) + (x >>> (32 - n));
		};
		hex = function (n) {
			return ("00" + n.toString(16)).slice(-2);
		};
		output_fn = function (n) {
			return hex(n & 255) + hex(n >>> 8) + hex(n >>> 16) + hex(n >>> 24);
		};
		shabal_f = function (start, w0, w1) {
			var i, j, k;
			for (i = 0; i < 16; i += 1) {
				B[i] = circ(B[i] + M[start + i], 17);
			}
			A[0] ^= w0;
			A[1] ^= w1;
			for (j = 0; j < 3; j += 1) {
				for (i = 0; i < 16; i += 1) {
					k = (i + 16 * j) % 12;
					A[k] = 3 * (A[k] ^ 5 * circ(A[(k + 11) % 12], 15) ^ C[(24 - i) % 16]) ^
						B[(i + 13) % 16] ^ (B[(i + 9) % 16] & ~ B[(i + 6) % 16]) ^ M[start + i];
					B[i] = circ(B[i], 1) ^ ~ A[k];
				}
			}
			for (j = 0; j < 36; j += 1) {
				A[j % 12] += C[(j + 3) % 16];
			}
			for (i = 0; i < 16; i += 1) {
				C[i] -= M[start + i];
			}
			k = B; 
			B = C; 
			C = k;
		};
		B = []; 
		C = [];
		M = [];
		for (z = 0; z < 16; z += 1) {
			B[z] = C[z] = 0;
			M[z] = 256 + z;
			M[z + 16] = 272 + z;
		}
		A = B.slice(4);
		shabal_f(0, -1, -1);
		shabal_f(16, 0, 0);
		ivA = A;
		ivB = B;
		ivC = C;
		return function (msg) {
			var i, j = 0;
			// clone the IV.
			A = ivA.slice(0);
			B = ivB.slice(0);
			C = ivC.slice(0);
			// pad the message with a byte 0x80 and then bytes 0x00 until you have
			// an integer number of 512-bit blocks.
			msg.push(0x80);
			while (msg.length % 64) {
				msg.push(0);
			}
			M = intify('le', msg, 'shabal');
			for (i = 0; i < M.length; i += 16) {
				j += 1;
				shabal_f(i, j, 0);
			}
			i -= 16;
			shabal_f(i, j, 0);
			shabal_f(i, j, 0);
			shabal_f(i, j, 0);
			return C.slice(8, 16).map(output_fn).join("");
		};
	}()),
	skein: (function () {
		var even, odd, charcode, zero, pad, rot, ubi, initial, state, mix, subkey_inject, L;
		L = function (lo, hi) {
			this.lo = lo ? lo : 0;
			this.hi = hi ? hi : 0;
		};
		L.clone = function (a) {
			return new L(a.lo, a.hi);
		};
		L.prototype = {
			xor: function (that) {
				this.lo ^= that.lo;
				this.hi ^= that.hi;
				return this;
			},
			plus: (function () {
				var two32, s;
				two32 = 4 * (1 << 30);
				s = function (x, y) {
					var t = x + y;
					if (x < 0) {
						t += two32;
					}
					if (y < 0) {
						t += two32;
					}
					return t;
				};
				return function (that) {
					this.lo = s(this.lo, that.lo);
					this.hi = (s(this.hi, that.hi) + (this.lo >= two32 ? 1 : 0)) % two32;
					this.lo = this.lo % two32;
					return this;
				};
			}()),
			circ: function (n) {
				var tmp, m;
				if (n >= 32) {
					tmp = this.lo;
					this.lo = this.hi;
					this.hi = tmp;
					n -= 32;
				} 
				m = 32 - n;
				tmp = (this.hi << n) + (this.lo >>> m);
				this.lo = (this.lo << n) + (this.hi >>> m);
				this.hi = tmp;
				return this;
			},
			toString: (function () {
				var hex, o;
				hex = function (n) {
					return ("00" + n.toString(16)).slice(-2);
				};
				o = function (n) {
					return hex(n & 255) + hex(n >>> 8) + hex(n >>> 16) + hex(n >>> 24);
				};
				return function () {
					return o(this.lo) + o(this.hi);
				};
			}())
		};
		//permutation constants
		even = [0, 2, 4, 6, 2, 4, 6, 0, 4, 6, 0, 2, 6, 0, 2, 4];
		odd = [1, 3, 5, 7, 1, 7, 5, 3, 1, 3, 5, 7, 1, 7, 5, 3];
		charcode = String.fromCharCode;
		zero = charcode(0);
		// padding string: 32 zero-characters, 64 zero-bytes.
		pad = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
		pad = pad.concat(pad);
		pad = pad.concat(pad);
		// rotation constants..
		rot = [
			[46, 36, 19, 37, 33, 27, 14, 42, 17, 49, 36, 39, 44, 9, 54, 56], 
			[39, 30, 34, 24, 13, 50, 10, 17, 25, 29, 39, 43, 8, 35, 56, 22]
		];
		subkey_inject = function (key, tweak, round) {
			for (var i = 0; i < 8; i += 1) {
				state[i].plus(key[(round + i) % 9]);
			}
			state[5].plus(tweak[round % 3]);
			state[6].plus(tweak[(round + 1) % 3]);
			state[7].plus(new L(round));
		};
		mix = function (r) {
			// input: one of the two arrays of round constants.
			var a, b, i;
			for (i = 0; i < 16; i += 1) {
				a = even[i];
				b = odd[i];
				state[a].plus(state[b]);
				state[b].circ(r[i]).xor(state[a]);
			}
		};
		// UBI calls on the chaining state c have a type number T (0-63), and some
		// data string D, while c is itself used as a Threefish32 key schedule.
		ubi = function (type, message) {
			var key, data, i, block, round, first, last, tweak, original_length;
			// the message is padded with zeroes and turned into 32-bit ints.
			// first we store the original length
			original_length = message.length;
			if (original_length % 64) {
				message = message.concat(pad.slice(original_length % 64));
			} else if (original_length === 0) {
				message = pad;
			}
			message = intify('le', message, 'skein');
			// then we construct the data array.
			data = [];
			for (i = 0; i < message.length; i += 2) {
				data.push(new L(message[i], message[i + 1]));
			}
			// we want a pointer last block, and tweak flags for first and type.
			first = 1 << 30;
			type <<= 24;
			last = data.length - 8;
			for (block = 0; block <= last; block += 8) {
				// tweak field. we're processing ints (block -> block + 8),
				// which each take up four bytes. On the last block we don't count
				// the padding 0's and we raise a "last" flag.
				tweak = (block === last) ? 
					[new L(original_length), new L(0, first + type + (1 << 31))] :
					[new L(8 * block + 64), new L(0, first + type)];
				// extended tweak field.
				tweak[2] = new L().xor(tweak[0]).xor(tweak[1]);
				
				// the key for threefish encryption is extended from the chaining state
				// with one extra value.
				key = state;
				key[8] = new L(0xa9fc1a22, 0x1bd11bda);
				for (i = 0; i < 8; i += 1) {
					key[8].xor(key[i]);
				}
				// and the state now gets the plaintext for this UBI iteration.
				state = data.slice(block, block + 8).map(L.clone);
				
				// Each "mix" is four "rounds" of threefish32, so the 18 here 
				// is essentially 4*18 = 72 in the spec.
				for (round = 0; round < 18; round += 1) {
					subkey_inject(key, tweak, round);
					mix(rot[round % 2]);
				}
				// there is then one final subkey addition in Threefish32:
				subkey_inject(key, tweak, round);
				// now we pass on to Matyas-Meyer-Oseas, XORing the source data
				// into the current state vector.
				for (i = 0; i < 8; i += 1) {
					state[i].xor(data[block + i]);
				}
				first = 0;
			}
		};
		state = [new L(), new L(), new L(), new L(), new L(), new L(), new L(), new L()];
		
		// ubi(0, "key string")
		ubi(4, [0x53, 0x48, 0x41, 0x33, 1, 0, 0, 0, 0, 2].concat(pad.slice(10, 32)));
		// ubi(8, "personalization as UTF-16, against the standard.");
		// ubi(12, "public key string, if such exists.");
		// ubi(16, "key identifier");
		// ubi(20, "nonce input");
		initial = state;
		return function (m) {
			state = initial.map(L.clone);
			ubi(48, m);
			ubi(63, [0,0,0,0, 0,0,0,0]);
			return state.join("");
		};
    }())
};