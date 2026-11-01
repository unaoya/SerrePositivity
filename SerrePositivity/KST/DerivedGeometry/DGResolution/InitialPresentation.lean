module

public import SerrePositivity.KST.DerivedGeometry.DGResolution.StagePresentation
public import SerrePositivity.DifferentialGraded.Resolution.Free.Evaluation

/-!
# 初期段階の閉じた自由生成元による表示

概要：初期の自由 dg 圏からの関手を、対象写像と全閉元生成辺の閉じた像で分類する。
方針：球の直和の普遍性と自由 dg 圏の有限語の普遍性を合成する。
規約：初期段階の Hom の微分は零であり、後続段階の指定微分の添加とは区別する。
使われ方：Drinfeld §13.4・Lemma 13.5 の半自由分解の初期段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w

namespace SerrePositivity.KST.DerivedGeometry.DGResolution

open CategoryTheory Limits
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/--
概要：閉元被覆の球の直和からの射は、各球生成元の閉じた像で指定できる。
方針：直和の包含と降下、および球からの射と閉元の全単射を使う。
規約：像の加法性を添字の閉元に関して要求しない。生成元は自由に添加する。
使われ方：Drinfeld §13.4・Lemma 13.5 の初期自由被覆。
-/
def cycleCoverHomEquiv (K L : Complex A) :
    (complexCycleCover A K ⟶ L) ≃
      (∀ j : ComplexCycleIndex A K, complexCycles A L j.1) where
  toFun f j := complexSphereCycle A j.1 (complexCycleCoverLift A K j.1 j.2 ≫ f)
  invFun z := Sigma.desc fun j => complexSphereMap A j.1 (z j)
  left_inv f := by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_comp_desc]
    exact (complexSphereHomEquiv A L j.1).symm_apply_apply
      (complexCycleCoverLift A K j.1 j.2 ≫ f)
  right_inv z := by
    funext j
    change complexSphereCycle A j.1
      (Sigma.ι (fun k : ComplexCycleIndex A K => complexSphere A k.1) j ≫
        Sigma.desc (fun k : ComplexCycleIndex A K => complexSphereMap A k.1 (z k))) = z j
    rw [Sigma.ι_comp_desc]
    exact (complexSphereHomEquiv A L j.1).apply_symm_apply (z j)

variable (D : Type v) [DGCategory A D] (E : Type w) [DGCategory A E]

/--
概要：初期自由 dg 圏の対象と各閉元生成辺の像のデータ。
方針：対象写像を選び、各生成元へ同じ次数の閉元を指定する。
規約：半自由性や分解の存在の証明をフィールドに置かない。
使われ方：Drinfeld §13.4・Lemma 13.5 の初期段階の普遍性。
-/
structure InitialCycleData where
  obj : D → E
  image : ∀ x y, ∀ j : ComplexCycleIndex A (homObject A D x y),
    complexCycles A (homObject A E (obj x) (obj y)) j.1

/--
概要：初期の生成辺の chain map と、閉元生成元の像は全単射に対応する。
方針：対象写像を保ち、各 Hom で球の直和の全単射を適用する。
規約：元の dg 圏の Hom に平坦性を要求しない。
使われ方：Drinfeld Lemma 13.5 の初期段階の自由な表示。
-/
def initialGeneratorEquiv :
    FreeDGCategory.GeneratorMap A D E (DGCategoryCycleCover.edges A D) ≃
      InitialCycleData A D E where
  toFun g := ⟨g.obj, fun x y => cycleCoverHomEquiv A _ _ (g.map x y)⟩
  invFun g := ⟨g.obj, fun x y => (cycleCoverHomEquiv A _ _).symm (g.image x y)⟩
  left_inv g := by
    cases g with
    | mk o f =>
      change (⟨o, fun x y => (cycleCoverHomEquiv A _ _).symm
        (cycleCoverHomEquiv A _ _ (f x y))⟩ :
          FreeDGCategory.GeneratorMap A D E (DGCategoryCycleCover.edges A D)) = ⟨o, f⟩
      congr 1
      funext x y
      exact (cycleCoverHomEquiv A _ _).symm_apply_apply (f x y)
  right_inv g := by
    cases g with
    | mk o f =>
      change (⟨o, fun x y => cycleCoverHomEquiv A _ _
        ((cycleCoverHomEquiv A _ _).symm (f x y))⟩ : InitialCycleData A D E) = ⟨o, f⟩
      congr 1
      funext x y
      exact (cycleCoverHomEquiv A _ _).apply_symm_apply (f x y)

variable [Small.{u} D]

/--
概要：初期自由 dg 圏からの関手は、対象写像と閉元生成辺の閉じた像で分類される。
方針：有限語の自由 dg 圏の普遍性と球生成元の評価を合成する。
規約：半自由分解の後続段階の自由添加と同じ具体的な生成元を使う。
使われ方：Drinfeld §13.4・Lemma 13.5 の初期段階。
-/
def initialFunctorEquiv :
    DGFunctor A (DGCategoryCycleCover.Source A D) E ≃ InitialCycleData A D E :=
  (FreeDGCategory.universalEquiv A D E (DGCategoryCycleCover.edges A D)).trans
    (initialGeneratorEquiv A D E)

end SerrePositivity.KST.DerivedGeometry.DGResolution
