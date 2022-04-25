class MIG:

    def __init__(this, mincode, complexity, arity, output_polarity, edges=None):
        this.mincode = mincode
        this.type = 'mig'
        this.complexity = complexity
        this.arity = arity
        this.output_polarity = output_polarity
        this.edges = edges
    
    def __init__(this, mks1):
        lines = mks1.splitlines()
        this.mincode = int(lines[0].strip())
        assert(lines[1] == 'mig')
        this.type = 'mig'
        this.complexity = int(lines[2].strip())

        l3 = lines[3].strip().split()
        this.arity = int(l3[0]) - this.complexity
        this.output_polarity = int(l3[1])

        #todo
        this.edges = None

    def to_mks1(this):
        return f'''{this.mincode}
{this.type}
{this.complexity}
{this.arity + this.complexity} {this.output_polarity}
{this.edges.join(" ")}
'''

