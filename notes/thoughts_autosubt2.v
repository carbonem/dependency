Considered using autosubst for unfoldings of global types and endpoints.
Decided against for two reasons:
- autosubst is good for simplifying equations with substitution expressions on both sides, which I have not run into yet. Unfoldings might be too simple to gain the benefits of autosubst
- The drawback is huge, we get big mutually recursive structure, must define induction principle ourselves. The representation doesn't capture that gType should be paramterized over some set of sendable values.
