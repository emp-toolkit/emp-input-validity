#ifndef IV_H__
#define IV_H__
#include <emp-tool/emp-tool.h>
#include "input-validity/elgamal.h"
#include <emp-ot/emp-ot.h>

class IV { public:
	const bool is_check = true;
	const bool is_evaluate = false;
	Elgamal *elgamal;
	NetIO * io;
	int party;
	int n1, n2, n3;
	PRG prg;
	PRP prp;
	MOTExtension * ot;
	Commitment commitment;
	const int ssp = 40;
	block *seed = nullptr, *key = nullptr, *key_seed = nullptr, *hcot_seed = nullptr;
	block * Y0 = nullptr;
	block * Y1 = nullptr;
	block * seed_Y0 = nullptr;
	block * seed_Y1 = nullptr;
	bool * choose = nullptr;
	PRG ** prgs = nullptr;
	block * deltas = nullptr;
	bool * input1;
	bool* input2;
	XorTree<> * xortree;
	~IV() {
		delete elgamal;
		delete ot;
		delete[] Y0;
		delete[] Y1;
		if(party == ALICE) {
			for(int i = 0; i < ssp+1; ++i) 
				delete prgs[i];
			delete[] prgs;
			delete[] seed;
			delete[] seed_Y0;
			delete[] seed_Y1;
			delete[] key;
			delete[] deltas;
			delete[] input1;
		} else {
			delete[] choose;
			delete[] key_seed;
			delete[] input2;
		}
		delete xortree;
	}

	IV(NetIO * io, int party, int n1, int _n2, int n3) {
		this->io = io;
		elgamal = new Elgamal(io, party, n1);
		this->party = party;
		this->n1 = n1;
		xortree = new XorTree<>(_n2);
		this->n2 = xortree->output_size();
		this->n3 = n3;
		Y0 = new block[n2*(ssp+1)];
		Y1 = new block[n2*(ssp+1)];
		ot = new MOTExtension(io);
		OTCO otco(io); 
		if(party == ALICE) {
			prgs = new PRG*[(ssp+1)];
			seed = new block[ssp+1];
			seed_Y0 = new block[n2];
			seed_Y1 = new block[n2];
			key = new block[ssp];
			deltas = new block[ssp+1];
			input1 = new bool[n1];
			prg.random_block(seed, ssp+1);
			prg.random_block(seed_Y0, n2);
			prg.random_block(seed_Y1, n2);
			prg.random_block(key, ssp);
			otco.send(key, seed, ssp);
			for(int j = 0; j < ssp+1; ++j) {
				prgs[j] = new PRG(&seed[j]);
				prgs[j]->random_block(&deltas[j], 1);
				deltas[j] = GarbleCircuit::make_delta(deltas[j]);
				for(int i = 0; i < n2; ++i) {
					prgs[j]->random_block(&Y0[i*(ssp+1)+j], 1);
				}
			}
			AES_KEY aes;
			block * tmp = new block[ssp+1];
			for(int i = 0; i < n2; ++i) {
				AES_set_encrypt_key(seed_Y0[i], &aes);
				memcpy(tmp, &Y0[i*(ssp+1)], (ssp+1)*sizeof(block));
				AES_ecb_encrypt_blks(tmp, ssp+1, &aes);
				io->send_block(tmp, ssp+1);

				AES_set_encrypt_key(seed_Y1[i], &aes);
				memcpy(tmp, &Y0[i*(ssp+1)], (ssp+1)*sizeof(block));
				for(int j = 0; j < ssp+1; ++j)
					tmp[j] = xorBlocks(tmp[j], deltas[j]);
				AES_ecb_encrypt_blks(tmp, ssp+1, &aes);
				io->send_block(tmp, ssp+1);
			}
			delete[] tmp;
		} else {
			input2 = new bool[n2];
			choose = new bool[ssp];
			key_seed = new block[ssp];
			uint8_t * c = new uint8_t[ssp];
			prg.random_data(c, ssp);
			for(int i = 0; i < ssp; ++i) {
				choose[i] = (c[i]%2 == 1);
			}
			delete[] c;
			otco.recv(key_seed, choose, ssp);

			for(int i = 0; i < n2; ++i) {
				io->recv_block(&Y0[i*(ssp+1)], ssp+1);
				io->recv_block(&Y1[i*(ssp+1)], ssp+1);
			}
		}
	}

	bool evalgAlice(void *f ) {
		bn_tpl* omegas = new bn_tpl[n3];
		eb_tpl* hs = new eb_tpl[n3];
		block (*L10) = new block[n1];
		block (*L11) = new block[n1];
		block *L1x = new block[n1];
		block *L2x = new block[n2];
		block *Lo = new block[n3];
		block * i2 = new block[xortree->input_size()];
		uint8_t * permute = new uint8_t[n1];
		uint8_t * loc = new uint8_t[n1];

		//step 15-17
		for(int i = 0; i < n3; ++i) {
			bn_newl(omegas[i][0], omegas[i][1]);
			eb_newl(hs[i][0], hs[i][1]);
			prg.random_bn(omegas[i][0]);
			bn_sub_mod(omegas[i][1], elgamal->w, omegas[i][1], elgamal->q);
			eb_mul_fix_norm(hs[i][0], elgamal->gTbl, omegas[i][0]);
			eb_mul_fix_norm(hs[i][1], elgamal->gTbl, omegas[i][1]);
			io->send_eb(hs[i], 2);
		}
		bn_t inEqChk;
		Hash hash;
		for(int j = 0; j < ssp; ++j) {
			io->set_key(&key[j]);
			eb_tpl u[2]; bn_t r[2];Com com[2];
			prgs[j]->random_data(permute, n1);
			for(int i = 0; i < n1; ++i){
				if(input1[i]) loc[i] = 1-(permute[i]%2);
				else loc[i] = (permute[i]%2);
			}
			io->send_data_enc(loc, n1);
			for(int i = 0; i < n1; ++i) {
				elgamal->commit(r[0], u[0], false, prgs[j]);
				elgamal->commit(r[1], u[1], true, prgs[j]);

				int ind = input1[i] ? 1 : 0;
				L10[i] = KDF(u[0][1]);//problem
				L11[i] = KDF(u[1][1]);//problem
				int p = (permute[i] %2);
				hash.reset();hash.put_eb(u[p], 2);
				hash.digest(com[p]);
				hash.reset();hash.put_eb(u[1-p], 2);
				hash.digest(com[1-p]);

				bn_sub_mod(inEqChk, elgamal->r[i], r[ind], elgamal->q);
				io->send_eb_enc(u[ind], 2);
				io->send_data(com[p], sizeof(Com));
				io->send_data(com[1-p], sizeof(Com));

				io->send_bn_enc(&inEqChk, 1);
			}

			HalfGateGen<NetIO, RTCktOpt::off> gc(io);
			gc.set_delta(deltas[j]);

			for(int i = 0; i < n2; ++i) {
				L2x[i] = Y0[i*(ssp+1)+j];
			}

			prgs[j]->random_block(L1x, n1);	
			gc.generic_to_xor(L1x, L10, L11, n1);
			local_gc = &gc;
			xortree->circuit(i2, L2x);
			run_function(f, Lo, L1x, i2);

			bn_tpl K, outRcvyDecom;
			eb_tpl outRcvyCom;
			block tmp[3];
			for(int i = 0; i < n3; ++i) {
				prgs[j]->random_bn(K, 2);
				eb_mul_fix_norm(outRcvyCom[0], elgamal->gTbl, K[0]);
				eb_mul_fix_norm(outRcvyCom[1], elgamal->gTbl, K[1]);
				eb_add_norm(outRcvyCom[0], outRcvyCom[0], hs[i][0]);
				eb_add_norm(outRcvyCom[1], outRcvyCom[1], hs[i][1]);
				io->send_eb(outRcvyCom, 2);

				bn_add_mod(outRcvyDecom[0], omegas[i][0], K[0], elgamal->q);
				bn_add_mod(outRcvyDecom[1], omegas[i][1], K[1], elgamal->q);
				io->send_bn_enc(outRcvyDecom, 2);

				for(int ind = 0; ind < 2; ++ind) {
					if (ind == 1) Lo[i] = xorBlocks(Lo[i], gc.delta);
					tmp[0] = tmp[1] = zero_block();
					int bn_size = bn_size_raw(K[ind]);
					bn_write_raw((uint64_t*)tmp, bn_size, K[ind]);
					tmp[0] = xorBlocks(prp.H(Lo[i], 0), tmp[0]);
					tmp[1] = xorBlocks(prp.H(Lo[i], 1), tmp[1]);
					tmp[2] = prp.H(Lo[i], 2);
					io->send_data(&bn_size, 4);
					io->send_block(tmp, 3);
				}
			}
		}
		delete[] i2;
		delete[] loc;
		delete[] permute;
		delete[] omegas;
		delete[] hs;
		delete[] L10;
		delete[] L11;
		delete[] L1x;
		delete[] L2x;
		delete[] Lo;
		return true;
	}

	bool evalgBob(void *f, bool * output) {
		eb_tpl* hs = new eb_tpl[n3];
		block *L1 = new block[n1];
		block *L1x = new block[n1];
		block *L2x = new block[n2];
		block *Lo = new block[n3];
		block (*L10) = new block[n1];
		block (*L11) = new block[n1];
		block * i2 = new block[xortree->input_size()];
		uint8_t * permute = new uint8_t[n1];
		uint8_t * loc = new uint8_t[n1];
		bool cheat = false;
		bool evaluated = false, recovered = false;
		for(int i = 0; i < n3; ++i) {
			io->recv_eb(hs[i], 2);
		}
		Hash hash;

		bn_t inEqChk;
		for(int j = 0; j < ssp; ++j) { 
			if (choose[j] == is_evaluate) {
				io->set_key(&key_seed[j]);
				eb_tpl u;
				Com com[2], com_chk;
				io->recv_data_enc(loc, n1);
				for(int i = 0; i < n1; ++i) {
					io->recv_eb_enc(u, 2);
					L1[i] = KDF(u[1]);//problem
					io->recv_data(com[0], sizeof(Com));
					io->recv_data(com[1], sizeof(Com));
					io->recv_bn_enc(&inEqChk, 1);
					if(!elgamal->check_eq(u, elgamal->com[i], inEqChk))
						cheat = true;
					hash.reset();hash.put_eb(u, 2);
					hash.digest(com_chk);
					if(strncmp(com[loc[i]], com_chk, sizeof(Com))!=0)
						cheat = true;
				}

				HalfGateEva<NetIO,RTCktOpt::off> gc(io);
				for(int i = 0; i < n2; ++i) {
					if (input2[i])
						L2x[i] = Y1[i*(ssp+1)+j];
					else 
						L2x[i] = Y0[i*(ssp+1)+j];
				}

				gc.generic_to_xor(L1x, L1, n1);
				local_gc = &gc;
				xortree->circuit(i2, L2x);
				run_function(f, Lo, L1x, i2);

				bn_tpl outRcvyDecom;
				eb_tpl outRcvyCom;eb_t tmp;
				block tmp_blocks[3];
				for(int i = 0; i < n3; ++i) {
					io->recv_eb(outRcvyCom, 2);
					io->recv_bn_enc(outRcvyDecom, 2);
					eb_mul_fix_norm(tmp, elgamal->gTbl, outRcvyDecom[0]);
					if (eb_cmp(tmp, outRcvyCom[0])!=CMP_EQ)
						cheat=true;
					eb_mul_fix_norm(tmp, elgamal->gTbl, outRcvyDecom[1]);
					if (eb_cmp(tmp, outRcvyCom[1])!=CMP_EQ)
						cheat=true;

					for(int ind = 0; ind < 2; ++ind) {
						block o = prp.H(Lo[i], 2);
						int bn_size;
						io->recv_data(&bn_size, 4);
						io->recv_block(tmp_blocks, 3);
						if(recovered) continue;
						if(block_cmp(&o, &tmp_blocks[2], 1)) {
							if(!evaluated)
								output[i] = (ind==1);
							else if (output[i] != (ind == 1)) {
								tmp_blocks[0] = xorBlocks(tmp_blocks[0], prp.H(Lo[i], 0));
								tmp_blocks[1] = xorBlocks(tmp_blocks[1], prp.H(Lo[i], 1));
								cout <<"recover input!"<<endl;
							}
						}
					}
				}
				evaluated = true;

			} else {
				io->set_key(nullptr);
				PRG seed_prg(&key_seed[j]);
				block delta_to_use;
				seed_prg.random_block(&delta_to_use, 1);
				seed_prg.random_block(L2x, n2);

				seed_prg.random_data(permute, n1);
				io->recv_data_enc(loc, n1);

				eb_tpl u[2];bn_t r[2];eb_tpl uchk;
				Com com[2];Com comchk[2];bn_t inEqChk;
				for(int i = 0; i < n1; ++i) {
					elgamal->commit(r[0], u[0], false, &seed_prg);
					elgamal->commit(r[1], u[1], true, &seed_prg);
					L10[i] = KDF(u[0][1]);//problem
					L11[i] = KDF(u[1][1]);//problem

					int p = permute[i]%2;
					hash.reset();hash.put_eb(u[p], 2);
					hash.digest(com[p]);
					hash.reset();hash.put_eb(u[1-p], 2);
					hash.digest(com[1-p]);
					io->recv_eb_enc(uchk, 2);
					io->recv_data(comchk[p], sizeof(Com));
					if(strncmp(comchk[p], com[p], sizeof(Com))!=0)
						cheat = true;
					io->recv_data(comchk[1-p], sizeof(Com));
					if(strncmp(comchk[1-p], com[1-p], sizeof(Com))!=0)
						cheat = true;
					io->recv_bn_enc(&inEqChk, 1);
				}

				char dgstgc[2][20];
				HashIO hashio(io);
				HalfGateEva<HashIO, RTCktOpt::off> gc(&hashio);
				gc.generic_to_xor(L1x, L1, n1);
				local_gc = &gc;
				xortree->circuit(i2, L2x);
				run_function(f, Lo, L1x, i2);
				hashio.get_digest(dgstgc[0]);
				
				HashIO hashio2(io);
				HalfGateGen<HashIO,RTCktOpt::off> gc2(&hashio2);
				gc2.set_delta(delta_to_use);

				seed_prg.random_block(L1x, n1);	
//				seed_prg.random_block(L1x, n1);	
				gc2.generic_to_xor(L1x, L10, L11, n1);
				local_gc = &gc2;
				xortree->circuit(i2, L2x);
				run_function(f, Lo, L1x, i2);
				hashio2.get_digest(dgstgc[1]);

				if(strncmp(dgstgc[0], dgstgc[1], 20)!=0)
					cheat = true;

				bn_tpl K, outRcvyDecom;
				eb_tpl outRcvyCom, outRcvyComChk;
				block tmp[3], tmp_chk[3];
				for(int i = 0; i < n3; ++i) {
					seed_prg.random_bn(K, 2);
					eb_mul_fix_norm(outRcvyCom[0], elgamal->gTbl, K[0]);
					eb_mul_fix_norm(outRcvyCom[1], elgamal->gTbl, K[1]);
					eb_add_norm(outRcvyCom[0], outRcvyCom[0], hs[i][0]);
					eb_add_norm(outRcvyCom[1], outRcvyCom[1], hs[i][1]);

					io->recv_eb(outRcvyComChk, 2);
					if(eb_cmp(outRcvyComChk[0], outRcvyCom[0])!=CMP_EQ)
						cheat = true;
					io->recv_bn_enc(outRcvyDecom, 2);

					for(int ind = 0; ind < 2; ++ind) {
						if (ind == 1) Lo[i] = xorBlocks(Lo[i], gc2.delta);
						tmp[0] = tmp[1] = zero_block();
						bn_write_raw((uint64_t*)tmp, bn_size_raw(K[ind]), K[ind]);
						tmp[0] = xorBlocks(prp.H(Lo[i], 0), tmp[0]);
						tmp[1] = xorBlocks(prp.H(Lo[i], 1), tmp[1]);
						tmp[2] = prp.H(Lo[i], 2);
						int bn_size;
						io->recv_data(&bn_size, 4);
						io->recv_block(tmp_chk, 3);
						if(!block_cmp(tmp, tmp_chk, 3))cheat=true;
					}
				}

			}
		}
		delete[] i2;
		delete[] loc;
		delete[] permute;
		delete[] hs;
		delete[] L1;
		delete[] L1x;
		delete[] L2x;
		delete[] L10;
		delete[] L11;
		delete[] Lo;
		return !cheat;
	}

	bool checkf1Bob(void * f) {
		eb_tpl* X = new eb_tpl[n1];
		block* X0lbl = new block[n1];
		block* X1lbl = new block[n1];
		block* Xlbl = new block[n1];
		block prg_seed, Z1, block_tmp;
		Com comZ;
		Decom decomZ;

		//Pick X, compute input label
		for(int i = 0; i < n1; ++i) {
			eb_newl(X[i][0], X[i][1]);
			elgamal->prg.random_eb(X[i][0], X[i][1]);
			X0lbl[i] = KDF(X[i][0]);
			X1lbl[i] = KDF(X[i][1]);
		}
		elgamal->send(X);
		if(f == nullptr) return true;
		//step 7.
		prg.random_block(&prg_seed, 1);
		PRG prg_loc(&prg_seed);
		prg_loc.random_block(Xlbl, n1);
		for(int i = 0; i < n1; ++i)
		  *((char *) &Xlbl[i]) &= 0xfe;

		PrivacyFreeGen<NetIO> gc(io);
		gc.privacy_free_to_xor(Xlbl, X0lbl, X1lbl, n1);
		local_gc = &gc;
		run_function(f, &block_tmp, Xlbl);
		io->recv_data(comZ, sizeof(Com));

		//step 8.
		io->send_block(&gc.delta, 1);
		io->send_block(&prg_seed, 1);
		elgamal->open();

		io->recv_data(decomZ, sizeof(Decom));
		io->recv_block(&Z1, 1);
		bool valid_com = commitment.open(decomZ, comZ, &Z1, sizeof(block));
		block_tmp = xorBlocks(block_tmp, gc.delta);
		bool f1ok = block_cmp(&Z1, &block_tmp, 1);

		delete[] X;
		delete[] Xlbl;
		delete[] X0lbl;
		delete[] X1lbl;
		return valid_com and f1ok;
	}

	bool checkf1Alice(bool * b, void * f) {
		eb_tpl * Xs = new eb_tpl[n1];
		eb_t * X = new eb_t[n1];
		block* X0lbl = new block[n1];
		block* X1lbl = new block[n1];
		block* Xlbl = new block[n1];
		memcpy(input1, b, n1);
		block block_tmp, prg_seed, delta, Z1;
		Com comL;Decom decomL;
		char hash_eval[20], hash_open[20];

		//step 4
		elgamal->recv(X, b);

		if(f == nullptr) return true;
		for(int i = 0; i < n1; ++i)
			Xlbl[i] = KDF(X[i]);	

		//step 7
		//io->set_hash_io();
		HashIO hashio(io);
		PrivacyFreeEva<HashIO> gc(&hashio);
		gc.privacy_free_to_xor(Xlbl, Xlbl, b, n1);
		local_gc = &gc;
		run_function(f, &Z1, Xlbl);
		hashio.get_digest(hash_eval);

		commitment.commit(decomL, comL, &Z1, sizeof(block));
		io->send_data(comL, sizeof(Com));

		//step 8
		io->recv_block(&delta, 1);
		io->recv_block(&prg_seed, 1);
		PRG prg_loc(&prg_seed);
		elgamal->open(Xs, b, X);

		for(int i = 0; i < n1; ++i) {
			X0lbl[i] = KDF(Xs[i][0]);
			X1lbl[i] = KDF(Xs[i][1]);
		}
		prg_loc.random_block(Xlbl, n1);
		for(int i = 0; i < n1; ++i)
		  *((char *) &Xlbl[i]) &= 0xfe;

		HashIO hashio2(io);
		PrivacyFreeGen<HashIO> gc2(&hashio2);
//		io->set_hash_io();
		gc2.set_delta(delta);
		local_gc = &gc2;
		gc2.privacy_free_to_xor(Xlbl, X0lbl, X1lbl, n1);
		run_function(f, &block_tmp, Xlbl);
		hashio2.get_digest(hash_open);
//		io->set_net_io();

		bool check_gc = (strncmp(hash_eval, hash_open, 20) == 0);
		io->send_data(decomL, sizeof(Decom));
		io->send_block(&Z1, 1);

		delete[] X;
		delete[] Xs;
		delete[] Xlbl;
		delete[] X0lbl;
		delete[] X1lbl;
		return check_gc;
	}


	bool checkf2Alice(void * f) {
		block res, Z2;
		Com comZ;
		Decom decomZ;
		block *Ylbl = new block[n2];

		ot->send(seed_Y0, seed_Y1, n2);

		if(f == nullptr) return true;
		for(int i = 0; i < n2; ++i) {
			Ylbl[i] = Y0[i*(ssp+1)+ssp];
			 *((char *) &Ylbl[i]) &= 0xfe;
		}

		PrivacyFreeGen<NetIO> gc(io);
		gc.set_delta(deltas[ssp]);
		local_gc = &gc;
		block * i2 = new block[xortree->input_size()];
		xortree->circuit(i2, Ylbl);
		run_function(f, &res, i2);
		io->recv_data(comZ, sizeof(Com));
		io->send_block(&seed[ssp], 1);
		io->recv_data(decomZ, sizeof(Decom));
		io->recv_block(&Z2, 1);
		bool valid_com = commitment.open
			(decomZ, comZ, &Z2, sizeof(block));

		res = xorBlocks(res, deltas[ssp]);
		bool f2ok = block_cmp(&Z2, &res, 1);

		delete[] i2;
		delete []Ylbl;
		return valid_com and f2ok;
	}

	bool checkf2Bob(bool * b, void * f) {
		block Z2, block_tmp, delta, prg_seed;
		xortree->gen(input2, b);

		Com comL;Decom decomL;
		char hash_eval[20], hash_open[20];
		block *Ylbl = new block[n2];
		block * seed_Y = new block[n2];

		ot->recv(seed_Y, input2, n2);
		AES_KEY aes;
		for(int i = 0; i < n2; ++i) {
			AES_set_decrypt_key(seed_Y[i], &aes);
			if (input2[i]) {
				AES_ecb_decrypt_blks(&Y1[i*(ssp+1)], ssp+1, &aes);
				Ylbl[i] = Y1[i*(ssp+1)+ssp];
			 *((char *) &Ylbl[i]) |= 0x1;
			}
			else  {
				AES_ecb_decrypt_blks(&Y0[i*(ssp+1)], ssp+1, &aes);
				Ylbl[i] = Y0[i*(ssp+1)+ssp];
			 *((char *) &Ylbl[i]) &= 0xfe;
			}
		}

		if(f == nullptr) return true;
		HashIO hashio(io);
//		io->set_hash_io();
		PrivacyFreeEva<HashIO> gc(&hashio);
		local_gc = &gc;
		block * i2 = new block[xortree->input_size()];
		xortree->circuit(i2, Ylbl);
		run_function(f, &Z2, i2);

		hashio.get_digest(hash_eval);
		commitment.commit(decomL, comL, &Z2, sizeof(block));
		io->send_data(comL, sizeof(Com));

		io->recv_block(&prg_seed, 1);
		PRG seed_prg(&prg_seed);
		seed_prg.random_block(&delta, 1);
		seed_prg.random_block(Ylbl, n2);
		for(int i = 0; i < n2; ++i)
			 *((char *) &Ylbl[i]) &= 0xfe;

		HashIO hashio2(io);
		PrivacyFreeGen<HashIO> gc2(&hashio2);
		gc2.set_delta(delta);
		local_gc = &gc2;
		xortree->circuit(i2, Ylbl);
		run_function(f, &block_tmp, i2);
		hashio2.get_digest(hash_open);
		bool check_gc = (strncmp(hash_open, hash_eval, 20) == 0);
		io->send_data(decomL, sizeof(Decom));
		io->send_block(&Z2, 1);

		delete[] i2;
		delete[] Ylbl;
		delete[] seed_Y;
		return check_gc;
	}


};
#endif// IV_H__
