using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace DigitalSignECC
{
    // класс параметров схемы цифровой подписи
    class DigitalSign
    {
        private BigInteger p = new BigInteger();
        private BigInteger a = new BigInteger();
        private BigInteger b = new BigInteger();
        // порядок подгруппы группы точек эллиптической кривой;
        private BigInteger q = new BigInteger();

        private byte[] xG;
        // точка эллептической кривой
        private ECPoint Q = new ECPoint();
        
        public DigitalSign(BigInteger p, BigInteger a, BigInteger b, BigInteger n, byte[] xG)
        {
            this.a = a;
            this.b = b;
            this.q = n;
            this.p = p;
            this.xG = xG;
        }

        //Генерируем секретный ключ заданной длины
        public BigInteger GenereatePrivateKey(int BitSize)
        {
            BigInteger d = new BigInteger();

            do
            {
                d.genRandomBits(BitSize, new Random());
            } while ((d < 0) || (d > q));

            return d;
        }

        //С помощью секретного ключа d вычисляем точку Q=d*G, это и будет наш публичный ключ
        public ECPoint GeneratePublicKey(BigInteger d)
        {
            ECPoint Q = ECPoint.multiply(d, QDecompression());
            return Q;
        }

        //Восстанавливаем координату y из координаты x и бита четности y 
        private ECPoint QDecompression()
        {
            byte y = xG[0];
            byte[] x = new byte[xG.Length-1];

            Array.Copy(xG, 1, x, 0, xG.Length - 1);

            BigInteger Xcord = new BigInteger(x);

            // y^2 = x^3 + a*x+b - эллип. уравнение
            BigInteger temp = (Xcord * Xcord * Xcord + a * Xcord + b) % p;

            BigInteger beta = ModSqrt(temp, p);
            BigInteger Ycord = new BigInteger();

            if ((beta % 2) == (y % 2))
                Ycord = beta;
            else
                Ycord = p - beta;

            ECPoint Q = new ECPoint();

            Q.a = a;
            Q.b = b;
            Q.FieldChar = p;
            Q.x = Xcord;
            Q.y = Ycord;

            this.Q = Q;

            return Q;
        }

        //функция вычисления квадратоного корня по модулю простого числа q
        public BigInteger ModSqrt(BigInteger a, BigInteger q)
        {
            BigInteger b = new BigInteger();

            do
            {
                b.genRandomBits(255, new Random());
            } while (Legendre(b, q) == 1);

            BigInteger s = 0;
            BigInteger t = q - 1;

            while ((t & 1) != 1)
            {
                s++;
                t = t >> 1;
            }

            BigInteger InvA = a.modInverse(q);
            BigInteger c = b.modPow(t, q);
            BigInteger r = a.modPow(((t + 1) / 2), q);
            BigInteger d = new BigInteger();

            for (int i = 1; i < s; i++)
            {
                BigInteger temp = 2;
                temp = temp.modPow((s - i - 1), q);

                d = (r.modPow(2, q) * InvA).modPow(temp, q);

                if (d == (q - 1))
                    r = (r * c) % q;
                c = c.modPow(2, q);
            }

            return r;
        }

        //вычисляем символ Лежандра
        public BigInteger Legendre(BigInteger a, BigInteger q)
        {
            return a.modPow((q - 1) / 2, q);
        }

        //подписываем сообщение
        // msg - сообщение
        // d - ключ подписи
        public string SingMsg(byte[] msg, BigInteger d)
        {
            // Шаг 2: вычислить e
            BigInteger e = new BigInteger(msg) % q;

            if (e == 0)
                e = 1;

            BigInteger k = new BigInteger();
            // точка эллиптической кривой
            ECPoint C = new ECPoint();

            BigInteger r = new BigInteger();
            BigInteger s = new BigInteger();

            do
            {
                // Шаг 3: сгенерировать случайное k (0< k <q)
                do
                {
                    k.genRandomBits(q.bitCount(), new Random());
                } while ((k < 0) || (k > q));

                // найти точку элл. C = kP
                C = ECPoint.multiply(k, Q);
                // и определить r = Xc(mod q)
                r = C.x % q;
                // определим s = (rd + ke)(mod q), s == 0 -> Шаг 3
                s = ((r * d) + (k * e)) % q;

            } while ((r == 0)||(s==0));

            // перевод значений в двоичный вид
            string Rvector = padding(r.ToHexString(),q.bitCount()/4);

            string Svector = padding(s.ToHexString(), q.bitCount() / 4);

            // конкатенацию двух двоичных векторов  (цифровая подпись)
            return Rvector + Svector;
        }

        //проверяем подпись 
        // H - хэш-сумма
        // sing - подпись
        // Q - ключ проверки подписи
        public bool SingVer(byte[] H, string sing, ECPoint Q)
        {
            // Шаг 1: вычисляем целые числа r и s по полученной подписи
            string Rvector = sing.Substring(0, q.bitCount() / 4);
            string Svector = sing.Substring(q.bitCount() / 4, q.bitCount() / 4);

            BigInteger r = new BigInteger(Rvector, 16);
            BigInteger s = new BigInteger(Svector, 16);

            if ((r < 1) || (r > (q - 1)) || (s < 1) || (s > (q - 1)))
                return false;

            // Шаг 3    
            BigInteger alpha = new BigInteger(H);
            BigInteger e = alpha % q;

            if (e == 0)
                e = 1;
            
            // Шаг 4
            BigInteger v = e.modInverse(q);

            // Шаг 5
            BigInteger z1 = (s * v) % q;
            BigInteger z2 = q + ((-(r * v)) % q);

            // восст. y по x
            this.Q = QDecompression();

            // Шаг 6: найти C = z1 P + z2 Q
            ECPoint A = ECPoint.multiply(z1, this.Q);
            ECPoint B = ECPoint.multiply(z2, Q);
            ECPoint C = A + B;
            // R = xc (mod q)
            BigInteger R = C.x % q;

            //Шаг 7
            if (R == r)
                return true;
            else
                return false;
        }

        //дополняем подпись нулями слева до длины n, где n - длина модуля в битах
        private string padding(string input, int size)
        {
            if (input.Length < size)
            {
                do
                {
                    input = "0" + input;
                } while (input.Length < size);
            }
            return input;
        }
    }
}
