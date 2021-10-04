# Graph Shrine

Extremely fast embedded graph databases maintained by dream shrine.

Optimized primarily for the operations needed for webs of trust.

### `CSRPlusPlus`

From [CSR++, A Fast, Scalable, Update-Friendly Graph Data Structure](https://hal.archives-ouvertes.fr/hal-03060095/document).

The fastest known graph database with these properties:

- concurrent
- mutable
- directed
- reverse edges are maintained

But it achieves this at the expense of also having these properties:

- native, embedded
- currently entirely in-memory, though it needs to be persisted at some point (I'll probably use capnp for a basically native but still standardized cross platform mem-mapping encoding)
- but it prioritizes read concurrency over write concurrency
- there's a slight latency before writes will be visible in reads, but they are strictly ordered
- though writes are very light, they are single-threaded, so if you're doing as many reads as writes, this is not tuned the way you want. It could be adapted to much much more write-heavy workloads trivially by putting RwLocks on the segments (and this was what the paper recommended, but I decided not to do that with this implementation because it is not ideal for web of trust queries. Segments still make sense as ways of limiting the length of edge vecs)

### `AdjacencyList`

Don't mind this, just a simple native graph used as an intermediary stage for assembling graphs that aren't as good at taking additions.