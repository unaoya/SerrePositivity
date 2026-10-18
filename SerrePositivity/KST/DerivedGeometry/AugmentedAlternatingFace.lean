module

public import SerrePositivity.KST.DerivedGeometry.AugmentedChainExact
public import SerrePositivity.KST.DerivedGeometry.AlternatingFaceFunctor
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
概要：増大単体対象の増大交代面鎖複体と関手による比較。
方針：標準の増大鎖写像を第0項へ挿入し、追加退化から完全性を証明する。
規約：余分な収縮や完全性を仮定として追加しない。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech 増大の分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v a b
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type u} [Category.{v} A] [Abelian A]

/--
概要：増大単体対象の交代面鎖複体へ増大先を第0項として挿入する。
方針：Mathlib の標準の増大写像と鎖複体の増大を使う。
規約：元の第n項は第n+1項へ移る。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech 分解。
-/
def augmentedAlternatingFaceComplex (X : SimplicialObject.Augmented A) : ChainComplex A ℕ :=
  ChainComplex.toSingle₀AsComplex _ _ (AlgebraicTopology.AlternatingFaceMapComplex.ε.app X)

/--
概要：追加退化を持つ増大単体対象の増大交代面鎖複体は全次数で完全。
方針：追加退化のホモトピー同値と増大鎖複体の完全性の定理を使う。
規約：零次数の全射性も含めて証明する。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech 分解。
-/
lemma augmentedAlternatingFace_acyclic {X : SimplicialObject.Augmented A}
    (ed : X.ExtraDegeneracy) : (augmentedAlternatingFaceComplex X).Acyclic := by
  let e := ed.homotopyEquiv
  exact chainAugment_acyclic_of_quasiIso e.hom

/--
概要：加法的関手は増大交代面鎖複体と自然な対象比較を持つ。
方針：各項の恒等同型と交代面複体の微分比較を使う。
規約：増大の第0項とその微分も比較に含める。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech の開上の評価。
-/
def augmentedAlternatingFaceMapIso {B : Type a} [Category.{b} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] (X : SimplicialObject.Augmented A) :
    (F.mapHomologicalComplex (.down ℕ)).obj (augmentedAlternatingFaceComplex X) ≅
      augmentedAlternatingFaceComplex
        (((SimplicialObject.Augmented.whiskering _ _).obj F).obj X) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => match n with
    | 0 => Iso.refl _
    | _ + 1 => Iso.refl _)
    (by
      intro i j hij
      have hi : j + 1 = i := hij
      subst i
      cases j with
      | zero =>
        simp [augmentedAlternatingFaceComplex, ChainComplex.toSingle₀AsComplex,
          ChainComplex.toSingle₀Equiv, ChainComplex.augment,
          SimplicialObject.Augmented.whiskering, SimplicialObject.Augmented.whiskeringObj]
      | succ j =>
        change 𝟙 _ ≫
            ((AlgebraicTopology.alternatingFaceMapComplex B).obj
              (((SimplicialObject.whiskering A B).obj F).obj X.left)).d (j + 1) j =
          F.map ((AlgebraicTopology.alternatingFaceMapComplex A).obj X.left |>.d (j + 1) j) ≫ 𝟙 _
        exact ((alternatingFaceCompMapIso F).app X.left).hom.comm (j + 1) j)

end SerrePositivity.KST.DerivedGeometry
