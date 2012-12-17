#include<iostream>
#include"vector.h"
#include"timeit.h"
#include"region.h"
#include"small_object_allocator.h"

struct point {
    static unsigned g_counter;
    unsigned m_p1, m_p2;
    point(unsigned p1, unsigned p2):m_p1(p1), m_p2(p2) {}
    ~point() { g_counter++; }
};

unsigned point::g_counter = 0;

static void tst_region(unsigned N, unsigned D, unsigned A) {
    timeit t(true, "region alloc");
    region r;
    ptr_vector<point> ps;
    for (unsigned i = 0; i < N; i++) {
        for (unsigned j = 0; j < D; j++) {
            r.push_scope();
            for (unsigned s = 0; s < A; s++) {
                ps.push_back(new (r) point(s, s));
            }
        }
        for (unsigned j = 0; j < D; j++) {
            for (unsigned s = 0; s < A; s++) {
                point * p = ps.back();
                ps.pop_back();
                p->~point();
            }
            r.pop_scope();
        }
    }
}

static void tst_small_alloc(unsigned N, unsigned D, unsigned A) {
    timeit t(true, "small alloc");
    small_object_allocator r("test");
    ptr_vector<point> ps;
    for (unsigned i = 0; i < N; i++) {
        for (unsigned j = 0; j < D; j++) {
            for (unsigned s = 0; s < A; s++) {
                ps.push_back(new (r) point(s, s));
            }
        }
        for (unsigned j = 0; j < D; j++) {
            for (unsigned s = 0; s < A; s++) {
                point * p = ps.back();
                ps.pop_back();
                p->~point();
                r.deallocate(sizeof(point), p);
            }
        }
    }
}

static void tst_default_alloc(unsigned N, unsigned D, unsigned A) {
    timeit t(true, "default alloc");
    ptr_vector<point> ps;
    for (unsigned i = 0; i < N; i++) {
        for (unsigned j = 0; j < D; j++) {
            for (unsigned s = 0; s < A; s++) {
                // ps.push_back(alloc(point, s, s));
                ps.push_back(new point(s, s));
            }
        }
        for (unsigned j = 0; j < D; j++) {
            for (unsigned s = 0; s < A; s++) {
                point * p = ps.back();
                ps.pop_back();
                // dealloc(p);
                delete p;
            }
        }
    }
}

void tst_alloc() {
    tst_region(1000, 100, 1000);
    tst_default_alloc(1000, 100, 1000);
    tst_small_alloc(1000, 100, 1000);
    std::cout << "counter: " << point::g_counter << "\n";
}
