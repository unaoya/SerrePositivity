module

public import SerrePositivity.KST.DerivedGeometry.OpenImmersionBase
public import SerrePositivity.KST.DerivedGeometry.TensorScalarTransport
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# 開埋め込みに沿う係数テンソル前層の輸送

概要：任意の開埋め込みに沿い、係数テンソル前層を自然同型で比較する。
方針：切断環の A 代数同型をテンソルし、appIso の自然性を使う。
規約：H は非可換でもよく、平坦性を要求しない。
使われ方：KST D4、Toën Derived Azumaya §3.2 のアフィン同型への輸送。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry

variable {A : Type u} [CommRing A] (H : Type u) [Ring H] [Algebra A H]
  {X Y : Scheme.{u}} (a : A →+* Γ(Y, ⊤)) (f : X ⟶ Y) [IsOpenImmersion f]

/--
概要：開埋め込みに沿う係数テンソルの各開での環同型。
方針：H 上の恒等同型と切断環の A 代数同型をテンソルする。
規約：切断の代数構造は明示した基礎環写像から作る。
使われ方：KST D4、Toën §3.2 の係数前層の同型の成分。
-/
def openImmersionTensorIsoAt (V : X.Opens) :
    (coefficientTensorPresheaf H (pullbackBaseMap a f)).obj (.op V) ≅
      (coefficientTensorPresheaf H a).obj (.op (f ''ᵁ V)) := by
  letI := sectionAlgebra (pullbackBaseMap a f) V
  letI := sectionAlgebra a (f ''ᵁ V)
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : H ≃ₐ[A] H)
    (openImmersionSectionAlgEquiv a f V)).toRingEquiv.toRingCatIso

/--
概要：開埋め込みの係数比較は純テンソルの切断を appIso の逆で送る。
方針：テンソル同型の定義を計算する。
規約：H の因子は変更しない。
使われ方：KST D4、Toën §3.2 の制限への自然性。
-/
lemma openImmersionTensorIsoAt_pure (V : X.Opens) (h : H) (s : Γ(X, V)) :
    (openImmersionTensorIsoAt H a f V).hom
      (tensorRingPure A H Γ(X, V) (sectionAlgebra (pullbackBaseMap a f) V) h s) =
    tensorRingPure A H Γ(Y, f ''ᵁ V) (sectionAlgebra a (f ''ᵁ V)) h
      ((f.appIso V).inv s) := rfl

/--
概要：開埋め込みによる係数テンソル前層の自然同型。
方針：純テンソルで制限と appIso の逆の自然性を使う。
規約：スキーム同型の場合も同じ比較を用いる。
使われ方：KST D4、Toën §3.2 の係数環層の同型への輸送。
-/
def openImmersionTensorPresheafIso :
    coefficientTensorPresheaf H (pullbackBaseMap a f) ≅
      f.opensFunctor.op ⋙ coefficientTensorPresheaf H a :=
  NatIso.ofComponents (fun V => openImmersionTensorIsoAt H a f V.unop)
    (fun {V W} i => by
      apply tensorRingObject_hom_ext A H Γ(X, V.unop)
        (sectionAlgebra (pullbackBaseMap a f) V.unop)
      intro h s
      change (openImmersionTensorIsoAt H a f W.unop).hom
          ((coefficientTensorPresheaf H (pullbackBaseMap a f)).map i
            (tensorRingPure A H Γ(X, V.unop)
              (sectionAlgebra (pullbackBaseMap a f) V.unop) h s)) =
        (coefficientTensorPresheaf H a).map (f.opensFunctor.map i.unop).op
          ((openImmersionTensorIsoAt H a f V.unop).hom
            (tensorRingPure A H Γ(X, V.unop)
              (sectionAlgebra (pullbackBaseMap a f) V.unop) h s))
      erw [coefficientTensorPresheaf_map_ringPure A H (pullbackBaseMap a f) i.unop h s,
        openImmersionTensorIsoAt_pure H a f W.unop,
        openImmersionTensorIsoAt_pure H a f V.unop,
        coefficientTensorPresheaf_map_ringPure A H a (f.opensFunctor.map i.unop)]
      exact congrArg (tensorRingPure A H Γ(Y, f ''ᵁ W.unop)
        (sectionAlgebra a (f ''ᵁ W.unop)) h)
          (congrArg (fun g : Γ(X, V.unop) ⟶ Γ(Y, f ''ᵁ W.unop) => g s)
            (f.appIso_inv_naturality i)))

/--
概要：開埋め込みの係数前層の比較は構造層からの射と可換。
方針：純テンソル 1 ⊗ s の計算式を使う。
規約：構造層の輸送を appIso の逆として明示する。
使われ方：KST D4、Toën §3.2 の係数環層の構造射の比較。
-/
lemma openImmersionTensorPresheafIso_unit :
    coefficientTensorUnit H (pullbackBaseMap a f) ≫
      (openImmersionTensorPresheafIso H a f).hom =
    openImmersionStructureMap f ≫
      Functor.whiskerLeft f.opensFunctor.op (coefficientTensorUnit H a) := by
  apply NatTrans.ext
  funext V
  apply RingCat.hom_ext
  apply RingHom.ext
  intro s
  exact openImmersionTensorIsoAt_pure H a f V.unop 1 s

end SerrePositivity.KST.DerivedGeometry
