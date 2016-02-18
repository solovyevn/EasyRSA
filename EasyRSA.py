#!/usr/bin/env python2
# -*- coding: utf-8 -*-
"""
Naive educational demo implementation of RSA algorithm to demonstrate the math
in RSA cryptosystem.
"""

from __future__ import unicode_literals

"""
Copyright (c) 2011, Nikita Solovyev
All rights reserved.

Redistribution and use in source and binary forms, with or without 
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, 
this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, 
this list of conditions and the following disclaimer in the documentation 
and/or other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its contributors 
may be used to endorse or promote products derived from this software without 
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" 
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE 
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE 
ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE 
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF 
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS 
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN 
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) 
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE 
POSSIBILITY OF SUCH DAMAGE.
"""

from sys import stdin
from codecs import encode, decode
from math import log, ceil, sqrt
from random import choice


def sieve_of_eratosthenes(max_int, min_int=2):
    """
    Computes a list of all prime numbers in range from `min_int` inclusive to 
    `max_int` exclusive, using simple Sieve of Eratosthenes algorithm.
    
    Args:
        max_int (long): Biggest integer to limit prime computation.
        min_int (Optional[long]): Smallest integer to limit prime computation.
                                  Defaults to 2.
    
    Returns:
        list: List of prime numbers in range from `min_int` inclusive to 
                `max_int` exclusive.
    """

    nums = dict.fromkeys(xrange(2, max_int), True)
    for i in xrange(2, long(ceil(sqrt(max_int)))):
        if nums[i]:
            j = 0
            k = i**2 + j*i
            while k <= max_int:
                nums[k] = False
                j+=1
                k = i**2 + j*i
    return [num for (num,val) in nums.iteritems() if val and num >= min_int]

    
def generate_primes(max_int):
    """
    Generates prime numbers p and q as a tuple `(p,q)`, each of which is 
    not greater then the `max_int` value.
    
    Args:
        max_int (long): Biggest integer to limit prime generation.
    
    Yiedls:
        (long, long): Two-tuple (p,q) containing two prime numbers.
    """
    
    primes = sieve_of_eratosthenes(max_int, 17)
    while primes:
        p = choice(primes)
        q = choice(primes)
        while p == q:
            q = choice(primes)
        if p>q:
            yield (p, q)
        else:
            yield (q, p)

        
def eiler_func(p, q):
    """
    Computes Euler's totient function for the modulus 'n' computed as `p`*`q`.
    
    Args:
        p (long): First modulus factor.
        q (long): Second modulus factor.
    
    Returns:
        long: Euler's totient function value for the modulus n=`p`*`q`.
    """
    
    phi = (p - 1) * (q - 1)
    return phi

    
def egcd(a, b):
    """
    Computes greatest common divisor (gcd) and coefficients of Bezout's identity
    for provided integers `a` and `b` using extended Euclidean Algorithm.
    
    Args:
        a (long): First integer number.
        b (long): Second integer number.
    
    Returns:
        (long, long, long): Three-tuple representing 
        (gcd, Bezout's identity coefficient, Bezout's identity coefficient).
    """
    
    r1=a
    r2=b
    s1=1
    s2=0
    t1=0
    t2=1
    while r2>0:
        q=r1//r2
        r=r1-q*r2
        r1=r2
        r2=r
        s=s1-q*s2
        s1=s2
        s2=s
        t=t1-q*t2
        t1=t2
        t2=t    
    return (r1,s1,t1)

    
def is_coprime(a, b):
    """
    Checks if provided prime numbers are coprime.
    
    Args:
        a (long): First prime number.
        b (long): Second prime number.
    
    Returns:
        bool: True if `a` and `b` are coprime and False otherwise.
    """

    if egcd(a, b)[0] == 1:
        return True
    else:
        return False
  
  
def mod_pow(base, exp, mod):
    """
    Computes modular exponentiation, integer `base` raised to the power of `exp`
    and divided by the modulus `mod`: `base`^`exp`(mod(`mod`)).
    
    Args:
        base (long): Exponentiation base integer value.
        exp (long): Power integer value.
        mod (long): Modulus positive integer value.
    
    Returns:
        long: Modular exponentiation result value.
    """
    
    c = 1
    e = 1
    while e <= exp:
        c = (c * base) % mod
        e += 1
    return c

    
def public_exp(phi):
    """
    Generates public exponent, denoted as 'e', for a given Euler's totient 
    function value `phi`, such that 1 < e < phi and gcd(e, phi) = 1.
    
    Args:
        phi (long): Euler's totient function value.
    
    Returns:
        long: Public exponent 'e' value.
    """
    
    primes = sieve_of_eratosthenes(phi)
    coprimes=[]
    for prime in primes:
        if is_coprime(phi, prime):
            coprimes.append(prime)
    e = choice(coprimes)
    return e

    
def secret_exp(e, phi):
    """
    Generates secret exponent, denoted as 'd', for a given public exponent value
    `e` and Euler's totient function value `phi`, such that e*d = 1(mod(phi)).
    
    Args:
        e (long): Public exponent value.
        phi (long): Euler's totient function value.
    
    Returns:
        long: Secret exponent 'd' value.
    """
    
    d = egcd(phi, e)[2]
    return d

    
def generate_keys(p, q):
    """
    Generates public and private key pair for the given prime numbers.
    
    Args:
        p (long): First prime number.
        q (long): Second prime number.
    
    Returns:
        ((long, long),(long, long)): Two-tuple of two-tuples, where first
        two-tuple represents public key (e, n) and second two-tuple represents
        private key (d, n).
    """
    
    n = p*q
    phi = eiler_func(p, q)
    d = -1
    while d < 0:
        e = public_exp(phi)
        d = secret_exp(e, phi)        
    public_key = (e, n)
    private_key = (d, n)
    return (public_key, private_key)

    
def encrypt(message, public_key):
    """
    Encrypts `message` with `public_key`.
    
    To ensure that RSA requirement 'm'<'n' is satisfied, the message is split in
    parts such, that each part is stored in a number of bits `n_bit_count`, 
    which is 1 less than the number of bits used to store the modulus 'n'.
    
    Args:
        message (byte string): Message string to encrypt.
        public_key (lond, long): Two-tuple representing public key in the form
                                 of ('public exponent', 'modulus').
    
    Returns:
        (byte string): Cipher string - encrypted message as a string of 
                       hexadecimal characters.
    """
    
    e,n = public_key
    #Count number of bits used for modulus 'n'
    n_bit_count = len(bin(n)[2:])
    #Transform message byte string to sequence of integers 'm' (message parts),
    #that satisfy 'm' < 'n'
    m_seq = string_to_intlist(message, n_bit_count-1)
    #Encrypt each message part 'm' to get a list of integers representing 
    #encrypted values of each message part, denoted 'c'
    c_seq = [mod_pow(m, e, n) for m in m_seq]
    #c_seq = map(lambda m: pow(m, e, n), m_seq)
    #Form a cipher byte string by transforming the list of integers to a string
    #of hexadecimal characters, accounting for the fact that each integer 
    #occupies no more bits than the modulus 'n'
    cipher = intlist_to_hexstr(c_seq, n_bit_count)
    return cipher

    
def decrypt(cipher, private_key):
    """
    Decrypts `cypher` with `private_key`.
    
    Args:
        cipher (byte string): Cipher string - encrypted message to decrypt, in 
                              the form of a string of hexadecimal characters, as
                              produced by `encrypt` function.
        private_key (lond, long): Two-tuple representing private key in the form
                                  of ('private exponent', 'modulus').
    
    Returns:
        (byte string): Decrypted message string.
    """
    
    d,n = private_key
    #Count number of bits used for modulus 'n'
    n_bit_count = len(bin(n)[2:])
    #Get a sequence of integers representing encrypted message parts 'c' from
    #cipher byte string of hexadecimal characters, accounting for the fact that 
    #each integer occupies no more bits than the modulus 'n'
    c_seq = hexstr_to_intlist(cipher, n_bit_count)
    #Decrypt each encrypted message part 'c' to get a list of integers
    #representing decrypted values of each original message part 'm'
    m_seq = [mod_pow(c, d, n) for c in c_seq]
    #m_seq = map(lambda c: pow(c, d, n), c_seq)
    #Transform sequence of integers representing decrypted message parts 'm' to
    #original message byte string
    message = intlist_to_string(m_seq, n_bit_count-1)
    return message

    
def intlist_to_hexstr(int_list, bit_count):
    """
    Transforms a list of integers `int_list` to a byte string of hexadecimal
    characters `hex_str`, assuming each integer must occupy `bit_count` bits, 
    and therefore each hexadecimal number in the string occupies constant number 
    of bits: greatest integer closest to `bit_count`/4.
        
    Args:
        int_list (list): List of integers to transform.
        bit_count (int): Number of bits each integer must occupy.
      
    Returns:
        (byte string): String of hexadecimal characters representing `int_list`.
    """

    #Form a format string accounting for the number of characters required to
    #represent possible biggest integer according to specified 'bit_count'
    f = str('%0' + str(int(ceil(bit_count/4.0))) + 'X')
    #Create a string of hexadecimal characters by joining a list of hexadecimal
    #representations of each integer in the list
    hex_str = str().join([f % item for item in int_list])
    return hex_str

    
def hexstr_to_intlist(hex_str, bit_count):
    """
    Transform a string of hexadecimal characters `hex_str`, representing integer
    numbers, to a list of integer numbers `int_list`, assuming each integer 
    number occupies `bit_count` bits, and therefore each hexadecimal number in
    the string occupies constant number of bits: greatest integer closest to 
    `bit_count`/4. Reverse function for `intlist_to_hexstr(int_list, bit_count)`.

    Args:
        hex_str (byte string): String of hexadecimal characters to transform to 
                               a list of integer numbers.
        bit_count (int): Number of bits each resulting integer must occupy.
    
    Returns:
        (list): List of integers represented by `hex_str`.
    """
    
    #Compute the number of characters each hexadecimal number in the string
    #occupies
    hex_chr_count = int(ceil(bit_count/4.0))
    #Create a list of integers by transforming each 'hex_chr_count' hexadecimal
    #characters to integer number
    int_list = [long(hex_str[i:i+hex_chr_count], 16) for i in xrange(0, 
                                                   len(hex_str), hex_chr_count)]
    return int_list
    
   
def string_to_intlist(str_in, bit_count):
    """
    Transforms a string 'str_in' to a list of integers, such that each resulting
    integer represents part of the `str_in` and it's value is stored using 
    the number of bits equal to `bit_count`. When there're not enough bits to 
    fill the size of `bit_count` zero padding is used.
        
    Args:
        str_in (byte string): String to transform to integers.
        bit_count (int): Number of bits each resulting integer must occupy.
    
    Returns:
        (list): List of integers representing `str_in`.
    """

    #Transform byte string to a string of bits representing the original string
    bit_str = str().join(bin(ord(ch))[2:].zfill(8) for ch in str_in)
    #Split string of bits to a list of 'bit_count' bits
    int_list = [bit_str[i:i+bit_count] for i in xrange(0, len(bit_str), 
                                                       bit_count)]
    #If the last element of the list contains less bits than 'bit_count' pad 
    #with zeroes
    if len(int_list[-1]) < bit_count:
        int_list[-1] += str('0')*(bit_count-len(int_list[-1]))
    #Transform a list of bits to list of integers
    int_list = [long(item, 2) for item in int_list] 
    return int_list

    
def intlist_to_string(int_list, bit_count):
    """
    Transforms a list of integers `int_list` representing parts of a string
    back to the string form, assuming each integer should occupy `bit_count`
    bits and zero padding was used to fill `bit_count` when the integer list was
    created, if required stripping of padding is performed.
    Reverse function for `string_to_intlist(str_in, bit_count)`.
        
    Args:
        int_list (list): List of integers representing the resulting string.
        bit_count (int): Number of bits each integer must occupy.
      
    Returns:
        (byte string): String that is represented by `int_list`.
    """
    
    #Transform list of integers to binary form, ensuring each integer occupies
    #'bit_count' bits and join in a string to form a string of bits
    bit_str = str().join(bin(item)[2:].zfill(bit_count) for item in int_list)
    #Transform string of bits into list of bytes
    chr_list = [chr(int(bit_str[i:i+8], 2)) for i in xrange(0, len(bit_str), 8)]
    #Joint list of bytes in a byte string and strip possible zero padding
    message = str().join(chr_list).rstrip(str('\x00'))
    return message
    
    
def main():
    """
    Main function for control loop
    
    Returns: 
        None
    """
    
    print('**************EasyRSA**************')
    print('*     Author: Nikita Solovyev     *')
    print('*          Version: 1.0           *')
    print('***********************************')
    print('')
    print('Welcome to EasyRSA!')
    while True:
        print('Type in the number corresponding to desired action:')
        print('0 - Exit')
        print('1 - Generate keys')
        print('2 - Encrypt message')
        print('3 - Decrypt message')
        print('4 - Run demo')
        variant = raw_input("Enter your choice:")
        if variant == '0':
            exit(0)
        elif variant == '1':
            while 1:
                maximum = raw_input("Enter the maximum integer for primes generation:")
                try:
                    maximum = long(maximum)
                    if maximum <= 19:
                        print("The smallest primes for using this program are 17 and 19, so 'maximum integer' value must be greater then 19!")
                        continue
                except:
                    print('Please enter integer!')
                    continue
                break
            primes_generator = generate_primes(maximum)
            p,q = next(primes_generator)
            print("Primes are: p=%d, q=%d" % (p, q))
            (public_key, private_key) = generate_keys(p,q)
            print("Public key: (%d,%d)" % public_key)
            print("Private key: (%d,%d)" % private_key)
        elif variant == '2':
            while 1:
                e = raw_input("Enter the public key exponent part:")
                try:
                    e = long(e)
                except:
                    print('Please enter integer!')
                    continue
                break
            while 1:
                n = raw_input("Enter the modulus:")
                try:
                    n = long(n)
                except:
                    print('Please enter integer!')
                    continue
                break
            while 1:
                message = decode(raw_input("Enter the message:"), stdin.encoding)
                if not message:
                    print("Message must not be empty!")
                    continue
                break
            public_key = (e,n)
            cipher = encrypt(encode(message, 'utf8'), public_key)
            print("Cipher:")
            print(cipher)
        elif variant == '3':
            while 1:
                d = raw_input("Enter the private key exponent part:")
                try:
                    d = long(d)
                except:
                    print('Please enter integer!')
                    continue
                break
            while 1:
                n = raw_input("Enter the modulus:")
                try:
                    n = long(n)
                except:
                    print('Please enter integer!')
                    continue
                break
            private_key = (d,n)
            while 1:
                cipher = decode(raw_input("Enter the cipher:"), stdin.encoding)
                if not cipher:
                    print("Cipher must not be empty!")
                    continue
                break
            message = decode(decrypt(encode(cipher, 'utf8'), private_key), 'utf8')
            print("Message:")
            print(message)
        elif variant == '4':
            while 1:
                maximum = raw_input("Enter the maximum integer for primes generation:")
                try:
                    maximum = long(maximum)
                    if maximum <= 19:
                        print("The smallest primes for using this program are 17 and 19, so 'maximum integer' value must be greater then 19!")
                        continue
                except:
                    print('Please enter integer!')
                    continue
                break
            while 1:
                message_in = decode(raw_input("Enter the message:"), stdin.encoding)
                if not message_in:
                    print("Message must not be empty!")
                    continue
                break
            primes_generator = generate_primes(maximum)
            p,q = next(primes_generator)
            print("Primes are: p=%d, q=%d" % (p,q))
            (public_key, private_key) = generate_keys(p,q)
            print("Public key: (%d,%d)" % public_key)
            print("Private key: (%d,%d)" % private_key)
            cipher = encrypt(encode(message_in, 'utf8'), public_key)
            print("Cipher:")
            print(cipher)
            message_out = decode(decrypt(cipher, private_key), 'utf8')
            print("Message:")
            print(message_out)
        else:
            print('Please enter the correct choice number!')
            continue
        continue
        
        
if __name__ == '__main__':
    main()
    exit(0)