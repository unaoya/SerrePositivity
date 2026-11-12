module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoEndpointTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws

/-!
概要：底を固定する元の射の指定比較を、全相対関手空間での後合成の関手同型へ移す。
方針：元の豊穣後合成で同じ頂点同型を送り、元の作用の頂点表示へ揃える。
規約：指定同型を選び直さない。使われ方：零面の指定三角形比較の始点についての自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C E Q : SSet.{u}} (p : C ⟶ B) (q : E ⟶ B) (r : Q ⟶ B)
  [LeftFibration q] [LeftFibration r] (f g : E ⟶ Q)
  (hf : f ≫ r = q) (hg : g ≫ r = q)
  (e : VertexIso (relativeFunctorVertex r q f hf) (relativeFunctorVertex r q g hg))
local notation "R" => relativeFunctorPostHom (Over.mk p) (Over.mk q) (Over.mk r)
local notation "Pf" => HomotopyLimits.relativeFunctorPost q r f hf p
local notation "Pg" => HomotopyLimits.relativeFunctorPost q r g hg p

/-- 元の底上の指定比較を、元の相対後合成の全関手同型へ値を保って移す。 -/
def relativeFunctorPostVertexIso : FunctorIso Pf Pg :=
  vertexIsoOfEq (VertexIso.map e R)
    (relativeFunctorPostHom_vertex (Over.mk p) (Over.mk q) (Over.mk r) (Over.homMk f hf))
    (relativeFunctorPostHom_vertex (Over.mk p) (Over.mk q) (Over.mk r) (Over.homMk g hg))

omit [LeftFibration q] [LeftFibration r] in
/-- 元の指定後合成の同型は、元の豊穣後合成による同じ指定値の像。 -/
lemma relativeFunctorPostVertexIso_heq_map :
    HEq (relativeFunctorPostVertexIso p q r f g hf hg e) (VertexIso.map e R) :=
  vertexIsoOfEq_heq _
    (relativeFunctorPostHom_vertex (Over.mk p) (Over.mk q) (Over.mk r) (Over.homMk f hf))
    (relativeFunctorPostHom_vertex (Over.mk p) (Over.mk q) (Over.mk r) (Over.homMk g hg))

/-- 全相対関手空間で元の始域比較を動かしても、元の指定後合成の比較は自然。 -/
lemma relativeFunctorPostVertexIso_naturality
    {x y : (relativeFunctorSpace q p) _⦋0⦌} (a : VertexIso x y) :
    VertexIso.map a Pf ≪≫ (relativeFunctorPostVertexIso p q r f g hf hg e).app y =
      (relativeFunctorPostVertexIso p q r f g hf hg e).app x ≪≫ VertexIso.map a Pg := by
  apply Iso.ext
  exact (relativeFunctorPostVertexIso p q r f g hf hg e).toNatIso.hom.naturality a.hom

end SerrePositivity.InfinityCategories.F2
