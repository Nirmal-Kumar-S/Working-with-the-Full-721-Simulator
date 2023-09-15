#include <inttypes.h>
#include <math.h>
#include <assert.h>
#include <iostream>
#include <vector>
#include "renamer.h"

using namespace std;

renamer::renamer(uint64_t n_log_regs_, uint64_t n_phys_regs_, uint64_t n_branches_, uint64_t n_active_)
{
	assert(n_phys_regs_>n_log_regs_);
	assert(n_active_ > 0);
    assert(n_branches_ >= 1);
    assert(n_branches_ <= 64);

	n_log_regs = n_log_regs_;
	n_phys_regs = n_phys_regs_;
    n_branches = n_branches_;
	n_active = n_active_;
	n_free = n_phys_regs - n_log_regs;
	
	RMT.resize(n_log_regs);
	AMT.resize(n_log_regs);
	PRF.resize(n_phys_regs);
	PRF_ready_bit.resize(n_phys_regs);

	for(int i=0;i<n_log_regs;i++)	
	{
		RMT[i]=i;
		AMT[i]=i;
	}
	
	for(int i=0;i<n_phys_regs;i++)
	{
		PRF[i]=0;
		PRF_ready_bit[i]=true;
	}
	
	active_head=active_tail=-1;
	active_list.resize(n_active);
	free_list.list.resize(n_free);
	free_list.head=0;
	free_list.tail=n_free-1;

	for(int i=n_log_regs;i<n_phys_regs;i++)
	{
		free_list.list[i-n_log_regs]=i;
	}
	
	GBM=0;
	
	branch_checkpoint.resize(n_branches);
	for(int i=0;i<n_branches;i++)
		branch_checkpoint[i].SMT.resize(n_log_regs);
}

bool renamer::stall_reg(uint64_t bundle_dst)
{
	int free_space=0;
	
	if(free_list.head==-1)
		free_space=0;
	else if(free_list.head<free_list.tail)
		free_space=free_list.tail-free_list.head+1;
	else
		free_space=n_free-(free_list.head-free_list.tail-1);	
			
	if((free_space)>=bundle_dst)
		return false;
	else
		return true;
}

bool renamer::stall_branch(uint64_t bundle_branch)
{
	uint64_t n=0, gbm=GBM;
	for(int i=0;i<n_branches;i++)
	{
		if(gbm&1)
			n++;
		gbm=gbm>>1;
		
	}
	if(bundle_branch>(n_branches-n))
		return true;
	else
		return false;
}

uint64_t renamer::get_branch_mask()
{
	return GBM;
}

uint64_t renamer::rename_rsrc(uint64_t log_reg)
{
	return RMT[log_reg];
}

uint64_t renamer::rename_rdst(uint64_t log_reg)
{
	assert(free_list.head!=-1);
	int position=free_list.head;

	if(free_list.head==free_list.tail)
		free_list.head=free_list.tail=-1;
	else
	{
		if(free_list.head==(n_free-1))
			free_list.head=0;
		else 
			free_list.head++;
	}
	
	RMT[log_reg]=free_list.list[position];
	return free_list.list[position];
}

uint64_t renamer::checkpoint()
{
	uint64_t gbm=GBM;
	int position;
	for(int i=0;i<n_branches;i++)
	{
		if(!(gbm&1))
		{
			position=i;
			break;	
		}
		gbm=gbm>>1;
	}
	
	assert(position<n_branches);
	copy_state(branch_checkpoint[position].SMT,RMT);
	branch_checkpoint[position].head=free_list.head;
	branch_checkpoint[position].recover_GBM=GBM;
	
	GBM|=1<<position;
	
	return position;	
}

bool renamer::stall_dispatch(uint64_t bundle_inst)
{
	int free_space=0;
	if(active_head==-1)
		free_space=0;
	else if(active_head<active_tail)
		free_space=active_tail-active_head+1;
	else
		free_space=n_free-(active_head-active_tail-1);	
	
	if((n_free-free_space)>=bundle_inst)
		return false;
	else
		return true;
}

uint64_t renamer::dispatch_inst(bool dest_valid, uint64_t log_reg, uint64_t phys_reg, bool load, bool store, bool branch, bool amo, bool csr, uint64_t PC) // Push active list
{
	assert(!(active_head==0&&active_tail==n_free-1)||(active_head==active_tail+1));
	
	if(active_tail==-1)
	{
		active_head=0;
		active_tail=0;
	}
	else 
	{
		if(active_tail==n_free-1)
			active_tail=0;
		else 
			active_tail++;
	}
	
	active_list[active_tail].destination_flag=dest_valid;
	if(active_list[active_tail].destination_flag)
	{
		active_list[active_tail].physical=phys_reg;
		active_list[active_tail].logical=log_reg;
	}
	active_list[active_tail].branch_flag=branch;
	active_list[active_tail].amo_flag=amo;
	active_list[active_tail].load_flag=load;
	active_list[active_tail].store_flag=store;
	active_list[active_tail].csr_flag=csr;
	active_list[active_tail].PC=PC;
	active_list[active_tail].branch_misprediction=false;
	active_list[active_tail].load_violation=false;
	active_list[active_tail].exception=false;
	active_list[active_tail].completed=false;
	active_list[active_tail].value_misprediction=false;
	return active_tail;
}

bool renamer::is_ready(uint64_t phys_reg)
{
	return PRF_ready_bit[phys_reg];
}

void renamer::clear_ready(uint64_t phys_reg)
{
	PRF_ready_bit[phys_reg]=false;
}

void renamer::set_ready(uint64_t phys_reg)
{
	PRF_ready_bit[phys_reg]=true;
}

uint64_t renamer::read(uint64_t phys_reg)
{
	return PRF[phys_reg];
}

void renamer::write(uint64_t phys_reg, uint64_t value)
{
	PRF[phys_reg]=value;
}

void renamer::set_complete(uint64_t AL_index)
{
	active_list[AL_index].completed=true;
}

void renamer::resolve(uint64_t AL_index, uint64_t branch_ID, bool correct)
{
	if(!correct)
	{
		active_tail=AL_index;
		free_list.head=branch_checkpoint[branch_ID].head;
		GBM=branch_checkpoint[branch_ID].recover_GBM;
		copy_state(RMT, branch_checkpoint[branch_ID].SMT);
	}
	else
	{
		uint64_t temp=1<<branch_ID;
		temp=~temp;
		GBM&=temp;
		for(int i=0;i<n_branches;i++)
		{
			branch_checkpoint[i].recover_GBM&=temp;
		}
	}
}

bool renamer::precommit(bool &completed, bool &exception, bool &load_viol, bool &br_misp, bool &val_misp,bool &load, bool &store, bool &branch, bool &amo, bool &csr,uint64_t &PC)
{
	if(active_head==-1)
		return false;
	else
	{
		completed=active_list[active_head].completed;
		exception=active_list[active_head].exception;
		load_viol=active_list[active_head].load_violation;
		br_misp=active_list[active_head].branch_misprediction;
		val_misp=active_list[active_head].value_misprediction;
		load=active_list[active_head].load_flag;
		store=active_list[active_head].store_flag;
		branch=active_list[active_head].branch_flag;
		amo=active_list[active_head].amo_flag;
		csr=active_list[active_head].csr_flag;
		PC=active_list[active_head].PC;
		return true;
	}
}

void renamer::commit() 
{
	assert(active_head!=-1);
	assert(active_list[active_head].completed==true);
	assert(active_list[active_head].exception==false);
	assert(active_list[active_head].load_violation==false);
	
	if(active_list[active_head].destination_flag)
	{
		uint64_t log=active_list[active_head].logical;
		uint64_t push=AMT[log];
		AMT[log]=active_list[active_head].physical;
		
		if(free_list.tail==-1)
			free_list.tail=free_list.head=0;
		else if(free_list.tail==n_free-1)
				free_list.tail=0;
			else 
				free_list.tail++;
		free_list.list[free_list.tail]=push;
	}

	if(active_head==active_tail)
		active_head=active_tail=-1;
	else if(active_head==n_free-1)
		active_head=0;
	else 
		active_head++;
}

void renamer::squash()
{
	active_head=active_tail=-1;
	free_list.tail=free_list.head-1;
	
	if(free_list.tail==-1)
		free_list.tail=n_free-1;
		
	copy_state(RMT, AMT);
	
	GBM=0;
	
	for(int i=0;i<n_phys_regs;i++)
	{
		PRF_ready_bit[i]=true;
	}
}

void renamer::set_exception(uint64_t AL_index)
{
	active_list[AL_index].exception=true;
}

void renamer::set_load_violation(uint64_t AL_index)
{
	active_list[AL_index].load_violation=true;
}

void renamer::set_branch_misprediction(uint64_t AL_index)
{
	active_list[AL_index].branch_misprediction=true;
}

void renamer::set_value_misprediction(uint64_t AL_index)
{
	active_list[AL_index].value_misprediction=true;
}

bool renamer::get_exception(uint64_t AL_index)
{
	return active_list[AL_index].exception;
}