#include <emp-tool>
#include "input-validity/iv.h"
#include <iomanip>
static int LEN1 = 512;
static int LEN2 = 512;
static int OUT_LEN = 160;
static char file[] = "circuits/files/sha-1.txt";
static CircuitFile cf(file);
//static char in1[] = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
//static char in2[] = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f";
//static char in3[] = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
//static char in4[] = "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89452821e638d01377be5466cf34e90c6cc0ac29b7c97c50dd3f84d5b5b5470917";
//static char out1[] = "92b404e556588ced6c1acd4ebf053f6809f73a93";
//static char out2[] = "b9ac757bbc2979252e22727406872f94cbea56a1";
static char out3[] = "bafbc2c87c33322603f38e06c3e0f79c1f1b1475";
//static char out4[] = "afb7bdad88b044c22688ded83ba7e1cc5ff41d4d";

void check1(Bit * res, Bit * in) {
	Bit * tmp = new Bit[160];
	cf.compute((block*)tmp, (block*)in, nullptr);
	string s = hex_to_binary(string(out3));
	res[0] = in[0];// & in[1];//(tmp[0] == (s[0] =='1'));
//	for(int i = 0; i < 160; ++i)
//		res[0] = res[0] & (tmp[i] == (s[i] =='1'));
	delete[] tmp;
}

void check2(Bit * res, Bit * in) {
	Bit * tmp = new Bit[160];
	cf.compute((block*)tmp, (block*)in, nullptr);
	string s = hex_to_binary(string(out3));
	res[0] = true;
	for(int i = 0; i < 160; ++i)
		res[0] = res[0] & (tmp[i] == (s[i] =='1'));
	delete[] tmp;
}

void compute(Bit * res, Bit * in, Bit * in2) {
	cf.compute((block*)res, (block*)in, (block*)in2);
}

int main(int argc, char** argv) {
	int port, party;
	parse_party_and_port(argv, &party, &port);

	NetIO * io = new NetIO(party==ALICE ? nullptr:"127.0.0.1", port);
	{
		void * c1 = (void *)(&check1);
		void * c2 = (void *)(&check2);
		void * c3 = (void *)(&compute);
		if (party == ALICE) {
			bool * b = new bool[LEN1];
			for(int i = 0; i < LEN1; ++i)
				b[i] = true;

			double t1 = wallClock();
			IV iv(io, party, LEN1, LEN2, OUT_LEN);
			bool b1 = iv.checkf1Alice(b, c1);
			bool b2 = iv.checkf2Alice(c2);
			bool b3 = iv.evalgAlice(c3);
			double t4 = wallClock();
			cout <<std::setprecision(4)<< "ALICE\t"<<LEN1<<"\t"<<(t4 - t1)<<"\t"<<b1<<b2<<b3<<endl;
			delete []b;
		}
		else {
			bool * b = new bool[LEN2];
			for(int i = 0; i < LEN2; ++i)
				b[i] = true;

			bool * output = new bool[OUT_LEN];
			double t1 = wallClock();
			IV iv(io, party, LEN1, LEN2, OUT_LEN);
			bool b1 = iv.checkf1Bob(c1);
			bool b2 = iv.checkf2Bob(b, c2);
			bool b3 = iv.evalgBob(c3, output);
			double t4 = wallClock();
			cout <<std::setprecision(4)<<LEN1<<"\t"<<LEN2<<"\t"<<OUT_LEN<<"\t"<<(t4 - t1)<<"\t"<<b1<<b2<<b3<<endl;
			for(int i = 0; i < OUT_LEN; ++i)
				cout << (output[i]? 1:0);
			cout <<endl;
			cout << hex_to_binary(string(out3))<<endl;
			delete []b;
		}
	}
	delete io;
	return 0;	
}
