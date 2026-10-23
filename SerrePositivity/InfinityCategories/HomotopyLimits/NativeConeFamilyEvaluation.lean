module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeComparisonTransport
public import SerrePositivity.InfinityCategories.Core.ConeFamily
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation

/-!
概要：元の slice の錐の族を全関手の族へ写したときの底制限と頂点評価。
方針：元の普遍族と join・直積の比較の包含上の式を使う。
規約：全次数で元の錐と元の頂点射影を保持する。
使われ方：元の極限錐への比較辺の可逆性を一点から検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の slice の全錐を全関手の族に表示する写像。 -/
def nativeConeFunctorFamily {K X : SSet.{u}} (D : K ⟶ X) :
    sliceOver D ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X :=
  sliceConeFamilyMap D ≫ vertexFiberι (coneRestriction K X) (functorVertex D)

/-- 全錐の族の底への制限は元の図式に厳密に定値。 -/
lemma nativeConeFunctorFamily_restriction {K X : SSet.{u}} (D : K ⟶ X) :
    nativeConeFunctorFamily D ≫ coneRestriction K X = SSet.const (functorVertex D) := by
  rw [nativeConeFunctorFamily, Category.assoc, vertexFiberι_comp, SSet.comp_const]

/-- 全錐の族を頂点で評価すると、元の slice の頂点射影を全次数で回収する。 -/
lemma nativeConeFunctorFamily_apex {K X : SSet.{u}} (D : K ⟶ X) :
    nativeConeFunctorFamily D ≫ evaluateFunctorAt (joinApexVertex K) =
      sliceOverProjection D := by
  let S := sliceOver D
  have hu : nativeConeFunctorFamily D = curry (sliceConeFamilyUncurry D) := rfl
  rw [hu, curry_evaluateFunctorAt_vertex]
  have hs : lift (SSet.const (joinApexVertex K)) (𝟙 S) ≫
      (β_ (join (Δ[0] : SSet.{u}) K) S).hom =
      lift (𝟙 S) (SSet.const (joinApexVertex K)) := rfl
  have hl : lift (𝟙 S) (SSet.const (joinApexVertex K)) =
      lift (𝟙 S) (SSet.const (stdSimplex.obj₀Equiv.symm 0)) ≫
        (S ◁ joinInl (Δ[0] : SSet.{u}) K) := by
    rw [lift_whiskerLeft, SSet.const_comp]
    rfl
  change lift (SSet.const (joinApexVertex K)) (𝟙 S) ≫
    (β_ (join (Δ[0] : SSet.{u}) K) S).hom ≫ joinTensorLeft S Δ[0] K ≫
      joinMap (fst S Δ[0]) (𝟙 K) ≫ sliceOverUncurry (𝟙 S) = _
  rw [← Category.assoc (lift _ _), hs, hl]
  simp only [Category.assoc]
  rw [← Category.assoc (S ◁ joinInl (Δ[0] : SSet.{u}) K), joinTensorLeft_inl]
  rw [← Category.assoc (joinInl (S ⊗ Δ[0]) K), joinInl_joinMap]
  simp only [Category.assoc]
  rw [sliceOverUncurry_projection, Category.id_comp,
    ← Category.assoc, lift_fst, Category.id_comp]

/-- 元の錐の頂点表示は、元の全関手の頂点と一致する。 -/
lemma nativeConeFunctorFamily_vertex {K X : SSet.{u}} {D : K ⟶ X} (c : JoinCone D) :
    (nativeConeFunctorFamily D).app (Opposite.op ⦋0⦌) c = functorVertex c.val :=
  congrArg Subtype.val (sliceConeFamilyMap_app_zero D c)

/-- 元の slice 内の辺を、元の全錐の間の関手辺として表示する。 -/
def nativeConeFunctorEdge {K X : SSet.{u}} {D : K ⟶ X} {c d : JoinCone D}
    (e : (sliceOver D).Edge c d) : SSet.Edge (functorVertex c.val) (functorVertex d.val) :=
  (e.map (nativeConeFunctorFamily D)).ofEq (nativeConeFunctorFamily_vertex c)
    (nativeConeFunctorFamily_vertex d)

/-- 比較辺の頂点成分は、元の slice 射影の辺と同じ全一単体。 -/
lemma nativeConeFunctorEdge_apex {K X : SSet.{u}} {D : K ⟶ X} {c d : JoinCone D}
    (e : (sliceOver D).Edge c d) :
    ((nativeConeFunctorEdge e).map (evaluateFunctorAt (joinApexVertex K))).edge =
      (e.map (sliceOverProjection D)).edge := by
  exact congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e.edge) (nativeConeFunctorFamily_apex D)

/-- 元の錐の比較辺の底図式への像は恒等辺と同じ全一単体を持ち、可逆。 -/
lemma nativeConeFunctorEdge_restriction_isInvertible {K X : SSet.{u}} [Quasicategory X]
    {D : K ⟶ X} {c d : JoinCone D} (e : (sliceOver D).Edge c d) :
    IsInvertibleEdge ((nativeConeFunctorEdge e).map (coneRestriction K X)) := by
  have he : ((nativeConeFunctorEdge e).map (coneRestriction K X)).edge =
      (SSet.Edge.id (functorVertex D)).edge := by
    exact congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) e.edge)
      (nativeConeFunctorFamily_restriction D)
  have hi : IsInvertibleEdge (SSet.Edge.id (functorVertex D)) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj X)) (functorVertex D)))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  exact (isInvertibleEdge_congr he).mpr hi

end SerrePositivity.InfinityCategories.HomotopyLimits
