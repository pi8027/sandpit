
require 'rubygems'
require 'rparsec'

class TypeInferError < StandardError ; end
class OccursCheckError < TypeInferError ; end

class Term

  def infer
    n, assump, const, type = constraints
    subst = {}
    solve(subst, const)
    assump2 = {}
    assump.each {|var, types|
      types.each{|t| solve(subst, n, t) }
      assump2[var] = n
      n = n+1
    }
    assump2.each {|v, t| assump2[v] = expand(t, subst) }
    [assump2 , expand(type, subst)]
  end

  private

  def solve(subst, c1, c2 = nil)
    if c2
      if subst.member?(c1)
        solve(subst, subst[c1], c2)
      elsif subst.member?(c2)
        solve(subst, c1, subst[c2])
      elsif c1 == c2
      elsif Fixnum === c1
        raise OccursCheckError if Array === c2 && c2.flatten.include?(c1)
        subst[c1] = c2
      elsif Fixnum === c2
        raise OccursCheckError if Array === c1 && c1.flatten.include?(c2)
        subst[c2] = c1
      elsif Array === c1 && Array === c2
        solve(subst, c1.zip(c2))
      end
    else
      c1.each{|l, r| solve(subst, l, r) }
    end
  end

  def expand(type, subst)
    if subst.member?(type)
      expand(subst[type], subst)
    elsif Fixnum === type
      type
    elsif Array === type
      type.map{|t| expand(t, subst) }
    end
  end

  class << self

    include RParsec
    include Parsers
    include Monad

    def parse(str)
      spaces = whitespace.many_
      var = word << spaces
      term = nil
      varexpr = (var << spaces).map{|v| VarTerm.new(v) }
      bracketexpr = char('(') >> spaces >> lazy{term} << char(')') << spaces
      factor = varexpr | bracketexpr
      app = sequence(factor, factor.many){|f, fs|
          fs.inject(f){|r, f| AppTerm.new(r, f) }
        }
      abs = sequence(char('\\') >> spaces >> var,
        string("->") >> spaces >> lazy{term}){|v, e|
          AbsTerm.new(v, e)
        }
      term = abs | app
      (spaces >> term).parse(str)
    end

    def type_to_str(type)
      if Fixnum === type
        type.to_s
      elsif Array === type
        "(" + Term.type_to_str(type[0]) + " -> " +
          Term.type_to_str(type[1]) + ")"
      end
    end

  end

end

class VarTerm < Term

  def initialize(var)
    @var = var
  end

  def constraints(n = 0)
    assump = Hash.new([])
    assump[@var] = [n]
    [n.succ, assump, [], n]
  end

end

class AppTerm < Term

  def initialize(t1, t2)
    @expr1, @expr2 = t1, t2
  end

  def constraints(n = 0)
    n1, a1, c1, t1 = @expr1.constraints(n.succ)
    n2, a2, c2, t2 = @expr2.constraints(n1)
    [n2, a1.merge(a2){|k, v1, v2| v1 + v2}, [[t1, [t2, n]]] + c1 + c2, n]
  end

end

class AbsTerm < Term

  def initialize(var, t)
    @var, @expr = var, t
  end

  def constraints(n = 0)
    n1, a1, c1, t1 = @expr.constraints(n.succ)
    constraints = a1[@var].map{|t| [n, t]} + c1
    a1.delete(@var)
    [n1, a1, constraints, [n, t1]]
  end

end

STDIN.each_line do |str|
  assump, type = Term.parse(str).infer
  assump.each{|v, t| puts v + " : " + Term.type_to_str(t) }
  puts "type : " + Term.type_to_str(type)
  puts ""
end

