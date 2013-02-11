/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    tactic_manager.cpp

Abstract:

    Collection of tactics & probes

Author:

    Leonardo (leonardo) 2012-03-06

Notes:

--*/
#include"tactic_manager.h"

tactic_manager::~tactic_manager() {
    finalize_tactic_cmds();
    finalize_probes();
}

void tactic_manager::insert(tactic_cmd * c) {
    symbol const & s = c->get_name();
    SASSERT(!m_name2tactic.contains(s));
    m_name2tactic.insert(s, c);
    m_tactics.push_back(c);
}

void tactic_manager::insert(probe_info * p) {
    symbol const & s = p->get_name();
    SASSERT(!m_name2probe.contains(s));
    m_name2probe.insert(s, p);
    m_probes.push_back(p);
}

static symbol norm_tactic_name(symbol const & s) {
    char const * n = s.bare_str();
    string_buffer<128> new_name;
    while (*n) {
        if (*n == '-')
            new_name.append("_");
        else if (*n >= 'A' && *n <= 'Z')
            new_name.append((*n - 'A') + 'a');
        else
            new_name.append(*n);
        n++;
    }
    return symbol(new_name.c_str());
}

tactic_cmd * tactic_manager::find_tactic_cmd(symbol const & s) const {
    tactic_cmd * c = 0;
    m_name2tactic.find(norm_tactic_name(s), c);
    return c;
}

probe_info * tactic_manager::find_probe(symbol const & s) const {
    probe_info * p = 0;
    m_name2probe.find(norm_tactic_name(s), p);
    return p;
}

void tactic_manager::finalize_tactic_cmds() {
    std::for_each(m_tactics.begin(), m_tactics.end(), delete_proc<tactic_cmd>());
    m_tactics.reset();
    m_name2tactic.reset();
}

void tactic_manager::finalize_probes() {
    std::for_each(m_probes.begin(), m_probes.end(), delete_proc<probe_info>());
    m_probes.reset();
    m_name2probe.reset();
}
