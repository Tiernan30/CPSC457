/******************************************************************************
    Copyright © 2012-2015 Martin Karsten

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
******************************************************************************/
#include "runtime/RuntimeImpl.h"
#include "runtime/Scheduler.h"
#include "runtime/Stack.h"
#include "runtime/Thread.h"
#include "kernel/Output.h"

// #include <chrono>
//std::chrono::seconds s (1);
//std::chrono::milliseconds ms = std::chrono::duration_cast<std::chrono::milliseconds> (s);
// Class for tree node
class ThreadNode{
	friend class Scheduler;
	Thread *th;
	
	public:
		bool operator < (ThreadNode other) const {
			return th->priority < other.th->priority;
		}
		bool operator == (ThreadNode other) const {
			return th->priority == other.th->priority;
		}
		bool operator > (ThreadNode other) const {
			return th->priority > other.th->priority;
		}
    
	//this is how we want to do it
	ThreadNode(Thread *t){
		th = t;
	}
}; 

//--------------
// AVL-tree implementation
// source: https://github.com/SuprDewd/CompetitiveProgramming/blob/master/code/data-structures/avl_tree.cpp
// note that the code on the github is very unreadable
// so most of the changes are removals of unused things,
// additions of the min node functions
// and making the code more readable.

// This code is by a student who was enrolled in CPSC 457 in Fall 2015
template <class T> class Tree {
public:
    struct node {
        T item; node *p, *l, *r;
        int size, height;
        node(const T &_item, node *_p = NULL) : item(_item), p(_p),
        l(NULL), r(NULL), size(1), height(0) { } };
    Tree() : root(NULL) { }
    node *root;
    
    bool empty() const {
		return root==NULL;
	}
    
    T* readMinNode() const {
        node *cur = root;
        while (cur->l){ cur=cur->l; }
        return &(cur->item);
    }
    
    T* popMinNode() {
        node *cur = root;
        while (cur->l){ cur=cur->l; }
        T* item = &(cur->item);
        erase(cur);
        return item;
    }
    
    node* find(const T &item) const {
        node *cur = root;
        while (cur) {
            if (cur->item < item) cur = cur->r;
            else if (item < cur->item) cur = cur->l;
            else break; }
        return cur; }
        
    void insert(const T &item) {
        node *prev = NULL, **cur = &root;
        while (*cur) {
            prev = *cur;
            if ((*cur)->item < item) cur = &((*cur)->r);
            else cur = &((*cur)->l);
        }
        node *n = new node(item, prev);
        *cur = n, fix(n);
		return;
	}
	
    void deleteNode(const T &item) {erase(find(item));}
    void erase(node *n) {
        if (!n) return;
        if (!n->l && n->r) parent_leg(n) = n->r, n->r->p = n->p;
        else if (n->l && !n->r) parent_leg(n) = n->l, n->l->p = n->p;
        else if (n->l && n->r) {
            node *s = successor(n);
            erase(s);
            s->p = n->p, s->l = n->l, s->r = n->r;
            if (n->l) n->l->p = s;
            if (n->r) n->r->p = s;
            parent_leg(n) = s, fix(s);
            return;
        } else parent_leg(n) = NULL;
        fix(n->p), n->p = n->l = n->r = NULL;
	}
	
    node* successor(node *n) const {
        if (!n) return NULL;
        if (n->r) return nth(0, n->r);
        node *p = n->p;
        while (p && p->r == n) n = p, p = p->p;
        return p;
	}
    
    node* nth(int n, node *cur = NULL) const {
        if (!cur) cur = root;
        while (cur) {
            if (n < sz(cur->l)) cur = cur->l;
            else if (n > sz(cur->l)) n -= sz(cur->l) + 1, cur = cur->r;
            else break;
        } return cur; }

private:
    inline int sz(node *n) const { return n ? n->size : 0; }
    inline int height(node *n) const { return n ? n->height : -1; }
    inline bool left_heavy(node *n) const {
        return n && height(n->l) > height(n->r); }
    inline bool right_heavy(node *n) const {
        return n && height(n->r) > height(n->l); }
    inline bool too_heavy(node *n) const {
		int hl = height(n->l);
		int hr = height(n->r);
        int m = hl>hr ? hl-hr : hr-hl;
        return n && m > 1;
    }

    node*& parent_leg(node *n) {
        if (!n->p) return root;
        if (n->p->l == n) return n->p->l;
        else  return n->p->r; //(n->p->r == n)
		
    }
    
    void augment(node *n) {
        if (!n) return;
        n->size = 1 + sz(n->l) + sz(n->r);
        int hl = height(n->l);
        int hr = height(n->r);
        int m = hl>hr ? hl : hr;
        n->height = 1 + m;
	}
    #define rotate(l, r) \
        node *l = n->l; \
        l->p = n->p; \
        parent_leg(n) = l; \
        n->l = l->r; \
        if (l->r) l->r->p = n; \
        l->r = n, n->p = l; \
        augment(n), augment(l)
    void left_rotate(node *n) { rotate(r, l); }
    void right_rotate(node *n) { rotate(l, r); }
    void fix(node *n) {
        while (n) { augment(n);
            if (too_heavy(n)) {
                if (left_heavy(n) && right_heavy(n->l)) left_rotate(n->l);
                else if (right_heavy(n) && left_heavy(n->r))
                    right_rotate(n->r);
                if (left_heavy(n)) right_rotate(n);
                else left_rotate(n);
                n = n->p; }
            n = n->p; } }
};
Scheduler::Scheduler() : readyCount(0), preemption(0), resumption(0), partner(this) {
  Thread* idleThread = Thread::create((vaddr)idleStack, minimumStack);
  idleThread->setAffinity(this)->setPriority(idlePriority);
  Scheduler::schedMinGranularity = 0;
  Scheduler::epochLength = 0;
  Scheduler::defaultEpochLength = 0; 
  Scheduler::minVRuntime = 0;
  Scheduler::vRuntime = 0;

  //Declare a tree
 Tree <ThreadNode> *readyTree;

	//Initialize the tree that contains the threads waiting to be served
 
 readyTree = new Tree<ThreadNode>();

  
  // use low-level routines, since runtime context might not exist
  idleThread->stackPointer = stackInit(idleThread->stackPointer, &Runtime::getDefaultMemoryContext(), (ptr_t)Runtime::idleLoop, this, nullptr, nullptr);
  readyQueue[idlePriority].push_back(*idleThread);
    //Add a thread to the tree. anyThreadClassObject is an object of ThreadClass
  readyTree->insert(*(new ThreadNode(idleThread)));
  readyCount += 1;
}








   
	


static inline void unlock() {}

template<typename... Args>
static inline void unlock(BasicLock &l, Args&... a) {
  l.release();
  unlock(a...);
}

// very simple N-class prio scheduling!
template<typename... Args>
inline void Scheduler::switchThread(Scheduler* target, Args&... a) {
  preemption += 1;
  CHECK_LOCK_MIN(sizeof...(Args));
  Thread* nextThread;
  readyLock.acquire();
  for (mword i = 0; i < (target ? idlePriority : maxPriority); i += 1) {
    if (!readyQueue[i].empty()) {
      nextThread = readyQueue[i].pop_front();
      readyCount -= 1;
      goto threadFound;
    }
  }
  readyLock.release();
  GENASSERT0(target);
  GENASSERT0(!sizeof...(Args));
  return;                                         // return to current thread

threadFound:
  readyLock.release();
  resumption += 1;
  Thread* currThread = Runtime::getCurrThread();
  GENASSERTN(currThread && nextThread && nextThread != currThread, currThread, ' ', nextThread);

  if (target) currThread->nextScheduler = target; // yield/preempt to given processor
  else currThread->nextScheduler = this;          // suspend/resume to same processor
  unlock(a...);                                   // ...thus can unlock now
  CHECK_LOCK_COUNT(1);
  Runtime::debugS("Thread switch <", (target ? 'Y' : 'S'), ">: ", FmtHex(currThread), '(', FmtHex(currThread->stackPointer), ") to ", FmtHex(nextThread), '(', FmtHex(nextThread->stackPointer), ')');

  Runtime::MemoryContext& ctx = Runtime::getMemoryContext();
  Runtime::setCurrThread(nextThread);
  Thread* prevThread = stackSwitch(currThread, target, &currThread->stackPointer, nextThread->stackPointer);
  // REMEMBER: Thread might have migrated from other processor, so 'this'
  //           might not be currThread's Scheduler object anymore.
  //           However, 'this' points to prevThread's Scheduler object.
  Runtime::postResume(false, *prevThread, ctx);
  if (currThread->state == Thread::Cancelled) {
    currThread->state = Thread::Finishing;
    switchThread(nullptr);
    unreachable();
  }
}

extern "C" Thread* postSwitch(Thread* prevThread, Scheduler* target) {
  CHECK_LOCK_COUNT(1);
  if fastpath(target) Scheduler::resume(*prevThread);
  return prevThread;
}

extern "C" void invokeThread(Thread* prevThread, Runtime::MemoryContext* ctx, funcvoid3_t func, ptr_t arg1, ptr_t arg2, ptr_t arg3) {
  Runtime::postResume(true, *prevThread, *ctx);
  func(arg1, arg2, arg3);
  Runtime::getScheduler()->terminate();
}

void Scheduler::enqueue(Thread& t) {
  GENASSERT1(t.priority < maxPriority, t.priority);
  readyLock.acquire();
  readyQueue[t.priority].push_back(t);
  bool wake = (readyCount == 0);
  readyCount += 1;
  readyLock.release();
  Runtime::debugS("Thread ", FmtHex(&t), " queued on ", FmtHex(this));
  if (wake) Runtime::wakeUp(this);
}

void Scheduler::resume(Thread& t) {
  GENASSERT1(&t != Runtime::getCurrThread(), Runtime::getCurrThread());
  if (t.nextScheduler) t.nextScheduler->enqueue(t);
  else Runtime::getScheduler()->enqueue(t);
}

void Scheduler::preempt() {               // IRQs disabled, lock count inflated
#if TESTING_NEVER_MIGRATE
 
  switchThread(this);
  Scheduler::minVRuntime = 1;
#else /* migration enabled */
  Scheduler* target = Runtime::getCurrThread()->getAffinity();

#if TESTING_ALWAYS_MIGRATE
  if (!target) target = partner;
#else /* simple load balancing */
  if (!target) target = (partner->readyCount + 2 < readyCount) ? partner : this;
#endif
  switchThread(target);
#endif

}

void Scheduler::suspend(BasicLock& lk) {
  Runtime::FakeLock fl;
  switchThread(nullptr, lk);
}

void Scheduler::suspend(BasicLock& lk1, BasicLock& lk2) {
  Runtime::FakeLock fl;
  switchThread(nullptr, lk1, lk2);
}

void Scheduler::terminate() {
  Runtime::RealLock rl;
  Thread* thr = Runtime::getCurrThread();
  GENASSERT1(thr->state != Thread::Blocked, thr->state);
  thr->state = Thread::Finishing;
  switchThread(nullptr);
  unreachable();
}




