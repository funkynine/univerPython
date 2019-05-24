# Ihor Bazyliuk 

from hashlib import sha256
from recordtype import recordtype
import random
from sympy import isprime

global Point
Point = recordtype("Point", "x y")

class elipticCurve:
    group = []
    infinity = Point(0,0)
    '''
        eliptic curve - y^2 = x^3+A*x+B
    '''
    def __init__(self, a, b, p):
        '''
            p - prime, E(a,b) - point that belongs to eliptic group
        '''
        self.a = a
        self.b = b
        self.prime = p
        assert (4*self.a**3+27*self.b**2 != 0),\
               'Can\'t get eliptic curve for E(%s, %s)'%(a, b)

    @property
    def prime(self):
        return self._prime
    
    @prime.setter    
    def prime(self, p):
        if p < 3:
            raise ValueError("p >= 3 required")
        elif isprime(p) == False:
            raise ValueError("P has to be a prime number")
        self._prime = p
        
    def is_on_eq(self, P):
        '''
            checking if point belongs to eliptic group
        '''
        if P == elipticCurve.infinity:
            return True
        return (P.y**2)%self._prime == (P.x**3+self.a*P.x+self.b)%self._prime
    
    def inv_mod(self, x, n):
        '''
            Inverse mod by Fermat's Little Theorem
        '''
        self.x = x
        if self.x%n == 0:
            raise ZeroDivisionError('Impossible inverse')
        return pow(self.x, n-2, n)
        
    def ec_inv(self, P):
        '''
            get inverse point to P on given eliptic curve
        '''
        if P == elipticCurve.infinity:
            return P
        return (-P.y)%self._prime

    def get_s(self, x):
        self.x = x
        return (self.x**3+self.a*self.x+self.b)%self.prime

    def ec_add(self, P, Q):
        '''
            Sum points of eliptic group, when P != Q
        '''        
        if P == elipticCurve.infinity:
            return Q
        elif Q == elipticCurve.infinity:
            return P
        elif Q == self.ec_inv(P):
            return elipticCurve.infinity
        
        lambda_ = ((Q.y - P.y) * self.inv_mod(Q.x - P.x, self._prime))%self._prime
        x = (lambda_**2 - P.x - Q.x) % self._prime
        y = (lambda_ * (P.x - x) - P.y) % self._prime
        return Point(x,y)

    def ec_double(self, P):
        '''
            Point doubling in case P == Q
        '''
        if P == elipticCurve.infinity:
            return Q
        
        lambda_ = ((3 * P.x**2 + self.a) * self.inv_mod(2 * P.y, self._prime))%self._prime
        x = (lambda_**2 - 2*P.x) % self._prime
        y = (lambda_ * (P.x - x) - P.y) % self._prime
        return Point(x,y)
      
    def double_and_add(self, G, n):
        '''
            G*n - binary calc format
        '''
        R = Point(0,0)        
        while n > 0:
            if n%2 == 1:
                R = self.ec_add(R, G)            
            G = self.ec_double(G)
            n = n//2
        return R

def factorize(n):
        '''
            factorizing composit number
        '''
        factors = []
        p = 2
        while True:
            while(n % p == 0 and n > 0):
                factors.append(int(p))
                n = n / p
            p += 1
            if p > n / p:
                break
        if n > 1:
            factors.append(int(n))
        return factors
    
def legandre_calc(s, p):
    if s >= p or s < 0:            
        return legandre_calc(s%p, p)
    
    elif s == 0 or s == 1:
        '''
            0mod(p) = 0;
            1mod(p) = 1
        '''
        return s
    
    elif (s**(1/2)).is_integer():
        '''
            if x = s**2 and s > 1 , L(s) == 1
        '''
        return 1
    
    elif s == 2:
        '''
            2/p = [1: (p = 8m+1, p = 8m+7); -1: (p = 8m+3, p = 8m+5)]
         '''
        if p%8 == 1 or p%8 == 7:
            return 1
        else:
            return -1
        
    elif s == p-1:
        '''
            (-1)/p = [1: p = 4m+1; -1: p = 4m+3]
        '''
        if p%4 == 1:
            return 1
        else:
            return -1
        
    elif isprime(s) == False:
        factors = factorize(s)
        product = 1            
        for pi in factors:                
            product *= legandre_calc(pi, p)
        return product
    else:            
        '''
            a < p
            a/p = (p/a)*(-1)**((p-1/2)*((a-1)/2))                
            TODO prevent self.p overwriting                
        '''   
        if ((p-1)/2)%2==0 or ((s-1)/2)%2==0:                
            return legandre_calc(p, s)
        else:
            return (-1)*legandre_calc(p, s)

def hash_digest(string, dtype="hex", charset="utf-8"):
    '''
        convert string to hash by sha256 algorithm
    '''
    m_byte = string if isinstance(string, bytes) else bytes(string, charset)
    digest_hex = sha256(m_byte).hexdigest()
    digest_int = int('0x'+digest_hex, 16)
    return digest_int

def int_binary_form(n):
    '''
        convert integer to binary array
    '''
    binary = bin(n)[2:]
    return [int(bit) for bit in binary]

class ECDSA:
    def __init__(self, Fn, i, G):
        self.F_n = Fn
        self.interval = i
        self.generator = G

    def generate_keys(self):
        '''
            private key generation
            ec - eliptic curve object
            G - point generator;            
        '''
        d_valid = False
        while (d_valid == False):
            d = random.getrandbits(self.interval)
            d_valid = 0 < d < self.F_n #check if belogns to finite field

        H = ECDSA.ec.double_and_add(self.generator, d)
        return (d, H)

    def sign(self, d, hash_m):
        '''
            d - private key; hash_m - hash value of message
        '''
        k_valid = False
        while (k_valid == False):
            k = random.getrandbits(self.interval)
            k_valid = 0 < k < self.F_n

        P = ECDSA.ec.double_and_add(self.generator, k)
        r = P.x % self.F_n
        if r == 0:
            self.sign(d, hash_m)
        else:
            k_inv = ECDSA.ec.inv_mod(k, self.F_n)
            s = (k_inv * (hash_m + d*r)%self.F_n)%self.F_n
            if s == 0:
                self.sign(d, hash_m)
            else:
                return (r,s)

    def verify(self, r, s, hash_m, pub_key):
        if (1 < r < self.F_n-1 and 1 < s < self.F_n-1):
            s_inv = ECDSA.ec.inv_mod(s, self.F_n)
            w = s_inv%self.F_n
            u1 = (hash_m*w)%self.F_n
            u2 = (r*w)%self.F_n

            P = ECDSA.ec.ec_add(ECDSA.ec.double_and_add(self.generator, u1),\
                                ECDSA.ec.double_and_add(pub_key, u2))
            v = P.x%self.F_n
            if v == r:
                return True
            return False
        else:
            return False
    
if __name__ == "__main__":
    while True:
        try:
            p = int(input('P = '))
            a = int(input('a = '))
            b = int(input('b = '))
            break
        except ValueError:
            print('Enter integers!')    
            
    ec = elipticCurve(a, b, p)
    p = ec.prime
    count = 0
    m = (p-3)//4            
    print('x', '\t', 'y^2', '\t', '(y^2)/p')
    print('-'*25)

    for x in range(0, p):
        s = ec.get_s(x)        
        L = legandre_calc(s, p)
        
        print('%-8s'%(x), '%s'%(s), '%10s'%(L))
        print('-'*25)        

        if L == 1:            
            P, Q = Point(x, (s**(m+1))%p), Point(x, -(s**(m+1))%p)            
            print('(%s, %s)'%(P.x, P.y), '(%s, %s)'%(Q.x, Q.y), sep="\n")

            ec.group.extend([P,Q])
            
        elif L == 0:
            P = Point(x, s)
            print('(%s, %s)'%(P.x, P.y))
            ec.group.append(P)

    count += len(ec.group)+1
    print('Points count + infinity (O): %s\n'%(count))
    print(ec.group)
    
    print('-'*20, 'ECDSA KEY PAIR GENERATION', '-'*20, end=' ')
    ECDSA.ec = ec #setting eliptic curve
    ecdsa = ECDSA(count, len(int_binary_form(count)), ec.group[random.randint(0, count-2)])
    (d,H) = ecdsa.generate_keys()
    print('\nGenerated private key (d):%s'%d)
    print('Generated public key (Hx, Hy): Hx = %s; Hy = %s'%(H.x, H.y))

    message = input('Message to sign: ')
    hash_int = hash_digest(message)
    print('-'*20, 'ECDSA MESSAGE SIGNATURE', '-'*20, end=' ')
    print('\nThe signed message: %s'%message)
    try:
        (r,s) = ecdsa.sign(d, hash_int)
    except TypeError:
        print("Message can't be signed with generated point")
    print('Result signature: \n r = %s; s = %s'%(r,s))

    print('-'*20, 'ECDSA MESSAGE VERIFICATION', '-'*20, end=' ')
    verify = ecdsa.verify(r, s, hash_int, H)
    print("\n(r,s) is a %s signature on '%s' using public key (%s, %s)"%(verify, message, H.x, H.y))
