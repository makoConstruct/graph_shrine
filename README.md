# Graph Shrine

Extremely fast embedded graph databases maintained by dream shrine.

Optimized primarily for the operations needed for webs of trust.

### `CSRPlusPlus`

From [CSR++, A Fast, Scalable, Update-Friendly Graph Data Structure](https://hal.archives-ouvertes.fr/hal-03060095/document).

Incomplete, roadmap:

- [x] implement the paper
- [x] test performance against `AdjacencyList`
	- that was disastrous. It's slower than an adjacencylist for graphs with a high branching factor and barely quicker (15%) for graphs with a low branching factor. This makes total sense, in retrospect, there will be very little memory adjacency benefits for highly random branching. However, random graphs are fairly unrealistic. It might perform better in the following task
	- [ ] test performance with the tasteweb user model data
- [ ] test performance against `petgraph::csr::Csr`
- [ ] make a HeaderVecWithGaps to eliminate one step of indirection
- [ ] finish integrating left-right and test parallel performance against other graph databases
- [ ] transition to a Capnp format for mem-mapping persistence

Will be the fastest known graph database with these properties:

- concurrent
- mutable
- directed
- reverse edges are maintained

It happens to have the properties:

- no parallel edges
- prioritizes read concurrency over write concurrency

But it achieves this at the expense of also having these properties:

- native, embedded
- currently entirely in-memory, though it needs to be persisted at some point (I'll probably use capnp for a basically native but still standardized cross platform mem-mapping encoding)
- there's a slight latency before writes will be visible in reads
- though writes are very light, they are single-threaded, so if you're doing as many reads as writes, this is not tuned the way you want. It could be adapted to much much more write-heavy workloads trivially by putting RwLocks on the segments (and this was what the paper recommended, but I decided not to do that with this implementation because it is not ideal for web of trust queries. Segments still make sense as ways of limiting the length of edge vecs)

### `AdjacencyList`

Don't mind this, just a simple native graph used as an intermediary stage for assembling graphs that aren't as good at taking additions (Csrs).