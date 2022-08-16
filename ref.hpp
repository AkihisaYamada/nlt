#ifndef _REF_HPP
#define _REF_HPP

template<typename T>
class Ref {
	struct Body {
		unsigned int nref;
		T body;
		Body() : nref(0) {}
		Body(T const& body) : nref(0), body(body) {}
	};
	Body* ptr;
	Ref(Body* ptr) : ptr(ptr) {}
public:
	Ref() : ptr(new Body()) {}
	Ref(T const& body) : ptr(new Body(body)) {}
	Ref(Ref const& org) : ptr(org.ptr) {
		ptr->nref++;
	}
	~Ref() {
		if( ptr->nref == 0 ) {
			delete ptr;
		} else {
			ptr->nref--;
		}
	}
	Ref& operator=(Ref const& other) {
		this->~Ref<T>();
		ptr = other.ptr;
		ptr->nref++;
		return *this;
	}
	T& operator*() const {
		return ptr->body;
	}
	T* operator->() const {
		return &ptr->body;
	}
	template<typename S>
	friend bool operator==(Ref<S> const& l, Ref<S> const& r);
};

template<typename T>
bool operator==(Ref<T> const& l, Ref<T> const& r) {
	return l.ptr == r.ptr || *l == *r;
};
#endif