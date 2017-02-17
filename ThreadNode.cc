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