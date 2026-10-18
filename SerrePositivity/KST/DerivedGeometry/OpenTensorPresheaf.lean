module

public import SerrePositivity.KST.DerivedGeometry.OpenBaseSections
public import SerrePositivity.KST.DerivedGeometry.TensorScalarTransport

/-!
# 係数テンソル前層の開制限

概要：開部分上で直接構成した係数テンソル前層を大域前層の制限と同定する。
方針：切断の代数構造の等式を移送し、純テンソルで自然性を確認する。
規約：環の同型として比較し、H の平坦性は要求しない。
使われ方：KST D4、Toën Derived Azumaya §3.2 のアフィン局所比較への接続。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry

variable {A : Type u} [CommRing A] (H : Type u) [Ring H] [Algebra A H]
  {X : Scheme.{u}} (a : A →+* Γ(X, ⊤)) (U : X.Opens)

/--
概要：開部分の各開で直接の係数テンソルと開像の係数テンソルを環として同定する。
方針：切断の A 代数構造の等式をテンソル環へ移す。
規約：切断の型の一致だけではスカラー作用を同一視しない。
使われ方：KST D4、Toën §3.2 の係数前層の開制限の比較。
-/
def openTensorPresheafIsoAt (V : U.toScheme.Opens) :
    (coefficientTensorPresheaf H (restrictedBaseMap a U)).obj (.op V) ≅
      (coefficientTensorPresheaf H a).obj (.op (U.ι ''ᵁ V)) := by
  change tensorRingObject A H Γ(U, V) (sectionAlgebra (restrictedBaseMap a U) V) ≅
    tensorRingObject A H Γ(U, V) (sectionAlgebra a (U.ι ''ᵁ V))
  exact eqToIso (congrArg (tensorRingObject A H Γ(U, V)) (sectionAlgebra_restrict a U V))

/--
概要：開制限のテンソル環の比較は純テンソルを保つ。
方針：代数構造の等式による移送の計算式を使う。
規約：第二因子の切断の値は変更しない。
使われ方：KST D4、Toën §3.2 の制限への自然性。
-/
lemma openTensorPresheafIsoAt_pure (V : U.toScheme.Opens) (h : H) (s : Γ(U, V)) :
    (openTensorPresheafIsoAt H a U V).hom
      (tensorRingPure A H Γ(U, V) (sectionAlgebra (restrictedBaseMap a U) V) h s) =
    tensorRingPure A H Γ(X, U.ι ''ᵁ V) (sectionAlgebra a (U.ι ''ᵁ V)) h s :=
  tensorRingPure_cast A H Γ(U, V) (sectionAlgebra_restrict a U V) h s

/--
概要：直接構成した係数テンソル前層と開像へ制限した係数テンソル前層は自然同型。
方針：各開の環同型を、純テンソル上の制限計算で束ねる。
規約：制限は開像の関手の反対による前合成。
使われ方：KST D4、Toën §3.2 の係数環層の開制限。
-/
def openTensorPresheafIso :
    coefficientTensorPresheaf H (restrictedBaseMap a U) ≅
      U.ι.opensFunctor.op ⋙ coefficientTensorPresheaf H a :=
  NatIso.ofComponents (fun V => openTensorPresheafIsoAt H a U V.unop)
    (fun {V W} i => by
      apply tensorRingObject_hom_ext A H Γ(U, V.unop)
        (sectionAlgebra (restrictedBaseMap a U) V.unop)
      intro h s
      change (openTensorPresheafIsoAt H a U W.unop).hom
          ((coefficientTensorPresheaf H (restrictedBaseMap a U)).map i
            (tensorRingPure A H Γ(U, V.unop)
              (sectionAlgebra (restrictedBaseMap a U) V.unop) h s)) =
        (coefficientTensorPresheaf H a).map (U.ι.opensFunctor.map i.unop).op
          ((openTensorPresheafIsoAt H a U V.unop).hom
            (tensorRingPure A H Γ(U, V.unop)
              (sectionAlgebra (restrictedBaseMap a U) V.unop) h s))
      erw [coefficientTensorPresheaf_map_ringPure A H (restrictedBaseMap a U) i.unop h s,
        openTensorPresheafIsoAt_pure H a U W.unop,
        openTensorPresheafIsoAt_pure H a U V.unop,
        coefficientTensorPresheaf_map_ringPure A H a (U.ι.opensFunctor.map i.unop)]
      rfl)

/--
概要：係数テンソル前層の開制限の同型は構造層からの単位と可換。
方針：純テンソル 1 ⊗ s の移送の式を使う。
規約：開部分の構造層は開像への前合成として扱う。
使われ方：KST D4、Toën §3.2 の係数環層の構造射の比較。
-/
lemma openTensorPresheafIso_unit :
    coefficientTensorUnit H (restrictedBaseMap a U) ≫
      (openTensorPresheafIso H a U).hom =
    Functor.whiskerLeft U.ι.opensFunctor.op (coefficientTensorUnit H a) := by
  apply NatTrans.ext
  funext V
  apply RingCat.hom_ext
  apply RingHom.ext
  intro s
  exact openTensorPresheafIsoAt_pure H a U V.unop 1 s

end SerrePositivity.KST.DerivedGeometry
