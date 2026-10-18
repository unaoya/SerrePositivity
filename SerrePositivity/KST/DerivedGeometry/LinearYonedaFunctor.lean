module

public import SerrePositivity.KST.DerivedGeometry.LinearYonedaComparison

/-!
概要：一般の線形加法圏の複体から代表 dg 加群への具体的な関手を構成する。
方針：閉零射との同値と実際の dg Yoneda を使い、関手の法則と完全忠実性を証明する。
規約：対象は実際の代表加群、射は具体的な後合成とする。
使われ方：Drinfeld §2.4、KST D4・§10-7 の有限 cell の代表可能性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CochainComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.KST.DerivedGeometry.LinearComplex

variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
attribute [local instance] enrichment
variable [Small.{u} (CochainComplex C ℤ)]

/--
概要：複体をその代表 dg 加群に送る関手。
方針：射は後合成とし、閉零の比較を通して関手の法則を確認する。
規約：複体の cone と加群の cone の比較で使う同じ射を採用する。
使われ方：Drinfeld §2.4、KST D4 の前三角化。
-/
def complexYoneda : CochainComplex C ℤ ⥤ ModuleCategory A (CochainComplex C ℤ) where
  obj X := ForgetEnrichment.of (Complex A) (representable A X)
  map f := representablePostcompose A f
  map_id X := by
    rw [representablePostcompose_eq_yoneda]
    have h : (closedHomEquiv A X X).symm (𝟙 X) = 𝟙 _ :=
      (closedHomEquiv A X X).injective (by simp [closedHomEquiv_id])
    rw [h]
    exact (dgYoneda A (CochainComplex C ℤ)).onClosed.map_id _
  map_comp {X Y Z} f g := by
    rw [representablePostcompose_eq_yoneda, representablePostcompose_eq_yoneda,
      representablePostcompose_eq_yoneda, ← CategoryTheory.Functor.map_comp]
    congr 1
    apply (closedHomEquiv A X Z).injective
    rw [Equiv.apply_symm_apply, closedHomEquiv_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/--
概要：具体的な代表加群への関手は充満。
方針：代表加群間の射の chain map による表示を使う。
規約：導来局所化前の射を扱う。
使われ方：Drinfeld §2.4、KST D4 の cone の帰納。
-/
instance complexYoneda_full : (complexYoneda (C := C) A).Full where
  map_surjective := representableHom_lift A

/--
概要：具体的な代表加群への関手は忠実。
方針：全 Hom の Yoneda 同型による閉零の忠実性と射の同値を使う。
規約：元の chain map の等式を反映する。
使われ方：Drinfeld §2.4、KST D4 の前三角化の比較。
-/
instance complexYoneda_faithful : (complexYoneda (C := C) A).Faithful where
  map_injective {X Y} f g h := by
    let : (dgYoneda A (CochainComplex C ℤ)).onClosed.Faithful :=
      (dgYoneda A (CochainComplex C ℤ)).onClosed_faithful_of_homIso
        (DGResolution.yoneda_hom_isIso A (CochainComplex C ℤ))
    change representablePostcompose A f = representablePostcompose A g at h
    rw [representablePostcompose_eq_yoneda, representablePostcompose_eq_yoneda] at h
    exact (closedHomEquiv A X Y).symm.injective
      ((dgYoneda A (CochainComplex C ℤ)).onClosed.map_injective h)

end SerrePositivity.KST.DerivedGeometry.LinearComplex
