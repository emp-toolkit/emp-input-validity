#include <emp-tool>
#include "input-validity/iv.h"
#include "bench/bench_input-check.h"
#include <iomanip>
const string circuit_file_location = macro_xstr(EMP_CIRCUIT_PATH);
static CircuitFile *cf;
static int len1;
static int len2;
static int len3;
static NetIO *io;
static int runs = 2;
int port, party;
void compute(Bit * res, Bit * in, Bit * in2) {
	cf->compute((block*)res, (block*)in, (block*)in2);
}
double bench_sha1() {
	len1 = 512;
	len2 = 0;
	len3 = 160;
	string file = circuit_file_location+"/sha-1.txt";
	cf = new CircuitFile(file.c_str());
	void * f = (void *)&compute;
	double res = bench_iv(nullptr, nullptr, f, len1, len2, len3, io, runs, party);
	delete cf;
	return res;
}

double bench_sha2() {
	len1 = 512;
	len2 = 0;
	len3 = 256;
	string file = circuit_file_location+"/sha-256.txt";
	cf = new CircuitFile(file.c_str());
	void * f = (void *)&compute;
	double res = bench_iv(nullptr, nullptr, f, len1, len2, len3, io, runs, party);
	delete cf;
	return res;
}

double bench_aes() {
	len1 = 128;
	len2 = 128;
	len3 = 128;

	string file = circuit_file_location+"/AES-non-expanded.txt";
	cf = new CircuitFile(file.c_str());
	void * f = (void *)&compute;
	double res = bench_iv(nullptr, nullptr, f, len1, len2, len3, io, runs, party);
	delete cf;
	return res;
}

double bench_add() {
	len1 = 32;
	len2 = 32;
	len3 = 33;
	string file = circuit_file_location+"/adder_32bit.txt";
	cf = new CircuitFile(file.c_str());
	void * f = (void *)&compute;
	double res = bench_iv(nullptr, nullptr, f, len1, len2, len3, io, runs, party);
	delete cf;
	return res;
}

int main(int argc, char** argv) {
	parse_party_and_port(argv, &party, &port);
	io = new NetIO(party==ALICE ? nullptr:SERVER_IP, port);
	cout << "ADD\t"<<bench_add()<<endl;
	cout << "AES\t"<<bench_aes()<<endl;
	cout << "SHA1\t"<<bench_sha1()<<endl;
	cout << "SHA2\t"<<bench_sha2()<<endl;
	delete io;
	return 0;	
}
