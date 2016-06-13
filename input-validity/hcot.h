#ifndef HCOT_H__
#define HCOT_H__
#include <2pctool/2pctool.h>

class HcOT {public:
	bn_t y, alpha0, alpha1;
	eb_t g[2][EB_TABLE_MAX];
	eb_t h[2][EB_TABLE_MAX];
	bn_t * r = nullptr;
	NetIO *io;
	bool sender;
	PRG prg;
	bn_t q;
	int K;
	PRG ** prgs = nullptr;
	int length;
	eb_tpl *Y = nullptr;
	HcOT(bool is_sender, NetIO * _io, int _k, int l, block * seed=nullptr) 
		: io(_io), sender(is_sender), K(_k), length(l) {
			initialize_relic();
			eb_curve_get_ord(q);
			if (is_sender) {
				prgs = new PRG*[K];
				for(int i = 0; i < K; ++i) {
					prgs[i] = new PRG(&seed[i]);
				}
				io->recv_eb((eb_t*)g, 2*EB_TABLE_MAX);
				io->recv_eb((eb_t*)h, 2*EB_TABLE_MAX);
			} else {
				eb_t tmp[2];
				for(int i = 0; i < 2; ++i) {
					prg.random_eb(tmp, 2);
					eb_mul_pre(g[i], tmp[0]);
					eb_mul_pre(h[i], tmp[1]);
				}
				io->send_eb((eb_t*)g, 2*EB_TABLE_MAX);
				io->send_eb((eb_t*)h, 2*EB_TABLE_MAX);
				r = new bn_t[length];
				prg.random_bn(r, length);
			}
		}
	~HcOT() {
		if(prgs!=nullptr) {
			for(int i = 0; i < K; ++i)
				delete prgs[i];
			delete[] prgs;
		}
		if(r!=nullptr) delete[] r;
		if(Y!=nullptr) delete[] Y;
	}

	void send(eb_tpl *L ) {
		eb_tpl *X = new eb_tpl[K*length];
		bn_tpl *r = new bn_tpl[K*length];
		bn_tpl *s = new bn_tpl[K*length];
		eb_t (*glT)[EB_TABLE_MAX] = new eb_t[length][EB_TABLE_MAX];
		eb_t (*hlT)[EB_TABLE_MAX] = new eb_t[length][EB_TABLE_MAX];
				eb_t tmp, tmp2;
		for(int i = 0; i < length; ++i) {
			io->recv_eb(&tmp, 1);
			eb_mul_pre(glT[i], tmp);
			io->recv_eb(&tmp, 1);
			eb_mul_pre(hlT[i], tmp);
		}

		for(int i = 0; i < length; ++i) {
			for(int j = 0; j < K; ++j) {
				prgs[j]->random_bn(r[i*K+j], 2);
				prgs[j]->random_bn(s[i*K+j], 2);
				for(int ind = 0; ind < 2; ++ind){
					eb_mul_fix_norm(X[i*K+j][ind], g[ind], r[i*K+j][ind]);
					eb_mul_fix_norm(tmp, h[ind], s[i*K+j][ind]);
					eb_add_norm(X[i*K+j][ind], X[i*K+j][ind], tmp);
				}
				io->send_eb(X[i*K+j], 2);
			}
		}

		for(int i = 0; i < length; ++i) {
			for(int j = 0; j < K; ++j) {
				for(int ind = 0; ind < 2; ++ind) {
					eb_mul_fix_norm(tmp, glT[i], r[i*K+j][ind]);
					eb_mul_fix_norm(tmp2, hlT[i], s[i*K+j][ind]);
					eb_add_norm(tmp, tmp2, tmp);
					eb_add_norm(tmp, tmp, L[i*K+j][ind]);
					io->send_eb(&tmp, 1);
				}
			}
		}
		delete[] X;
		delete[] r;
		delete[] s;
		delete glT;
		delete hlT;
	}


	void recv(eb_t * L, bool * b) {
		eb_t g_loc, h_loc;
		Y = new eb_tpl[K*length];
		for(int i = 0; i < length; ++i) {
			int ind = b[i] ? 1: 0;
			eb_mul_fix_norm(g_loc, g[ind], r[i]);
			io->send_eb(&g_loc, 1);
			eb_mul_fix_norm(h_loc, h[ind], r[i]);
			io->send_eb(&h_loc, 1);
		}

		eb_tpl *X = new eb_tpl[K*length];
		for(int i = 0; i < length; ++i) {
			for(int j = 0; j < K; ++j) {
				io->recv_eb(X[i*K+j], 2);
				int ind = b[i] ? 1: 0;
				eb_mul_norm(X[i*K+j][ind], X[i*K+j][ind], r[i]);
			}
		}

		for(int i = 0; i < length; ++i) {
			for(int j = 0; j < K; ++j) {
				io->recv_eb(Y[i*K+j], 2);
				int ind = b[i] ? 1: 0;
				eb_sub_norm(L[i*K+j], Y[i*K+j][ind], X[i*K+j][ind]);
			}
		}
		delete[] X;
	}

	void open(eb_tpl* Xs, const eb_t* old_X, block seed, bool *b, int index) {
		PRG seed_prg(&seed);
		bn_tpl s, t;
		for(int i = 0; i < length; ++i) {
			seed_prg.random_bn(s, 2);
			seed_prg.random_bn(t, 2);
			int ind = b[i] ? 1 : 0;
			eb_copy(Xs[i*K+index][ind], old_X[i*K+index]);
			eb_t tmp;
			bn_mul_mod(s[1-ind], s[1-ind], r[i], q);
			eb_mul_fix_norm(tmp, g[ind], s[1-ind]);
			bn_mul_mod(t[1-ind], t[1-ind], r[i], q);
			eb_mul_fix_norm(Xs[i*K+index][1-ind], h[ind], t[1-ind]);
			eb_add_norm(Xs[i*K+index][1-ind], Xs[i*K+index][1-ind], tmp);
			eb_sub_norm(Xs[i*K+index][1-ind], Y[i*K+index][1-ind], Xs[i*K+index][1-ind]);
		}
	}
};

#endif
