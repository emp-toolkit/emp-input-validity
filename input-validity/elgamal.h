#ifndef ELGAMAL_H__
#define ELGAMAL_H__
#include <emp-tool/emp-tool.h>

class Elgamal{ public:
	NetIO * io;
	eb_t g, h;
	eb_t hTbl[EB_TABLE_MAX];
	const eb_t * gTbl;
	bn_t w, q;
	int party;
	PRG prg;
	int length;
	Elgamal(NetIO * io, int party, int length) 
		: io(io), party(party) , length(length) {
		initialize_relic();
		eb_newl(g, h);
		bn_newl(w, q);
		eb_curve_get_ord(q);
		eb_curve_get_gen(g);
		gTbl = eb_curve_get_tab();
		assert(setup_omega());
		eb_mul_pre(hTbl, h);
	}
	bool setup_omega() {
		if(party == ALICE) {
			bn_t r, c;
			bn_newl(r, c, w);
			prg.random_bn(r, w);
			eb_t t; 
			eb_newl(t);
			eb_mul_fix_norm(h, gTbl, w);
			eb_mul_fix_norm(t, gTbl, r);
			io->send_eb(&h, 1);
			io->send_eb(&t, 1);
			io->recv_bn(&c, 1);
			bn_mul_mod(c, c, w, q);
			bn_add_mod(c, c, r, q);
			io->send_bn(&c, 1);
			return true;
		} else {//BOB
			eb_t t, hc, gs; 
			bn_t c, s;
			eb_newl(t, hc, gs);
			bn_newl(c, s);
			prg.random_bn(c);
			io->recv_eb(&h, 1);
			io->recv_eb(&t, 1);
			io->send_bn(&c, 1);
			io->recv_bn(&s, 1);
			eb_mul_norm(hc, h, c);
			eb_mul_fix_norm(gs, gTbl, s);
			eb_add_norm(hc, hc, t);
			return (eb_cmp(hc, gs)==CMP_EQ);	
		}
	}

	~Elgamal(){
		if(r!= nullptr)
			delete[] r;
		if(com!=nullptr)delete[] com;
	}

	eb_tpl *com = nullptr, *nA = nullptr, *nB = nullptr;
	bn_tpl *elgl_s = nullptr, *elgl_t = nullptr;
	bn_t * r = nullptr;
	void commit(bn_t r, eb_tpl com, bool b, PRG * prg) {
		prg->random_bn(r);
		eb_mul_fix_norm(com[0], gTbl, r);
		eb_mul_fix_norm(com[1], hTbl, r);
		if(b) eb_add_norm(com[1], com[1], g);
	}
	bool check_eq(eb_tpl new_com, eb_tpl old_com, bn_t r_diff) {
		eb_t tmp;
		eb_mul_fix_norm(tmp, gTbl, r_diff);
		eb_add_norm(tmp, new_com[0], tmp);
		if(eb_cmp(tmp, old_com[0])!=CMP_EQ)
			return false;

		eb_mul_fix_norm(tmp, hTbl, r_diff);
		eb_add_norm(tmp, new_com[1], tmp);
		if(eb_cmp(tmp, old_com[1])!=CMP_EQ)
			return false;
		return true;	
	}	
	void send(eb_tpl* X) {
		nA = new eb_tpl[length];
		nB = new eb_tpl[length];
		eb_t tmp; eb_newl(tmp);
		com = new eb_tpl[length];
		elgl_s = new bn_tpl[length];
		elgl_t = new bn_tpl[length];
		for(int i = 0; i < length; ++i) {
			prg.random_bn(elgl_s[i][0], elgl_s[i][1], elgl_t[i][0], elgl_t[i][1]);
			eb_mul_fix_norm(nA[i][0], gTbl, elgl_s[i][0]);//A0=g^s0
			eb_mul_fix_norm(tmp, hTbl, elgl_t[i][0]);
			eb_add_norm(nA[i][0], nA[i][0], tmp);//A0 = g^s0h^t0

			eb_mul_fix_norm(nA[i][1], gTbl, elgl_s[i][1]);//A1=g^s1
			eb_mul_fix_norm(tmp, hTbl, elgl_t[i][1]);
			eb_add_norm(nA[i][1], nA[i][1], tmp);//A1 = g^s1h^t1

			io->recv_eb(com[i], 2);
			eb_mul_norm(nB[i][0], com[i][0], elgl_s[i][0]);
			eb_mul_norm(tmp, com[i][1], elgl_t[i][0]);
			eb_add_norm(nB[i][0], nB[i][0], tmp);
			eb_add_norm(nB[i][0], nB[i][0], X[i][0]);

			eb_mul_norm(nB[i][1], com[i][0], elgl_s[i][1]);
			eb_sub_norm(tmp, com[i][1], g);
			eb_mul_norm(tmp, tmp, elgl_t[i][1]);
			eb_add_norm(nB[i][1], nB[i][1], tmp);
			eb_add_norm(nB[i][1], nB[i][1], X[i][1]);
		}

		for(int i = 0; i < length; ++i) {
			io->send_eb(nA[i], 2);
			io->send_eb(nB[i], 2);
		}
		delete[] nA;
		delete[] nB;
	}

	void open( ) {
		for(int i = 0; i < length; ++i) {
			io->send_bn(elgl_s[i], 2);
			io->send_bn(elgl_t[i], 2);
		}
		delete[] elgl_s;
		delete[] elgl_t;
	}

	void recv(eb_t* X, bool * b) {
		nA = new eb_tpl[length];
		nB = new eb_tpl[length];
		r = new bn_t[length];
		eb_tpl com;
		for(int i = 0; i < length; ++i) {
			commit(r[i], com, b[i], &prg);
			io->send_eb(com, 2);
		}

		for(int i = 0; i < length; ++i) {
			io->recv_eb(nA[i], 2);
			io->recv_eb(nB[i], 2);
			int ind = b[i]? 1: 0;
			eb_mul_norm(X[i], nA[i][ind], r[i]);
			eb_sub_norm(X[i], nB[i][ind], X[i]);
		}
	}

	void open(eb_tpl* Xs, bool * b, eb_t * X) {
		bn_tpl s, t;
		eb_t Ar, gt;
		for(int i = 0; i < length; ++i) {
			io->recv_bn(s, 2);
			io->recv_bn(t, 2);
			int ind = b[i]? 1:0;
			eb_copy(Xs[i][ind], X[i]);
			eb_mul_norm(Ar, nA[i][1-ind], r[i]);
			eb_sub_norm(Ar, nB[i][1-ind], Ar);
			eb_mul_fix_norm(gt, gTbl, t[1-ind]);
			if(ind == 1) {
				eb_sub_norm(Xs[i][1-ind], Ar, gt);
			} else {
				eb_add_norm(Xs[i][1-ind], Ar, gt);
			}
		}
		delete[] nA;
		delete[] nB;
	}
	void recovery(bool* b, bn_t omega) {
		for(int i = 0; i < length; ++i) {
			eb_mul_norm(com[i][0], com[i][0], omega);
			b[i] = (eb_cmp(com[i][0], com[i][1]) != CMP_EQ);
		}
	}
}; 
#endif// PKFC_H__