module

public import SerrePositivity.KST.DerivedBlowup.ExteriorConeComponents

/-!
概要：KST Def3.1 の生成元追加後の Koszul 外積複体を既存 mappingCone と同定する。
方針：項ごとの二成分同型と微分行列 (-d,0;a,d) を使う。
規約：最後の生成元を左から外積し、cone は最後の関係式のスカラー作用の錐。
使われ方：有限列の反復 cone 比較の帰納段階。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Limits HomologicalComplex homotopyCofiber

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：生成元追加後の外積と cone の項同型は微分と可換。
方針：cone の二つの射影を合成し、証明済みの cochain 微分行列と比較する。
規約：KST Def3.1。使われ方：mappingCone との複体同型。 -/
theorem exteriorToConeXIso_comm (d : M →ₗ[R] R) (a : R) (q : ℤ) :
    (exteriorKoszulCochain (exteriorProductDifferential d a)).d q (q + 1) ≫
        (exteriorToConeXIso d a (q + 1)).hom =
      (exteriorToConeXIso d a q).hom ≫ (exteriorScalarCone d a).d q (q + 1) := by
  apply ext_to_X (smulId a (exteriorKoszulCochain d)) (q + 1) (q + 1 + 1) rfl
  · simp only [Category.assoc, exteriorToConeXIso_fst]
    change _ = (exteriorToConeXIso d a q).hom ≫
      homotopyCofiber.d (smulId a (exteriorKoszulCochain d)) q (q + 1) ≫ _
    rw [d_fstX _ q (q + 1) (q + 1 + 1) rfl rfl]
    simp only [Preadditive.comp_neg, ← Category.assoc, exteriorToConeXIso_fst]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact congrArg Prod.fst (exteriorProductCochainEquiv_d d a q z)
  · simp only [Category.assoc, exteriorToConeXIso_snd]
    change _ = (exteriorToConeXIso d a q).hom ≫
      homotopyCofiber.d (smulId a (exteriorKoszulCochain d)) q (q + 1) ≫ _
    rw [d_sndX _ q (q + 1) rfl]
    simp only [Preadditive.comp_add, ← Category.assoc,
      exteriorToConeXIso_fst, exteriorToConeXIso_snd]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact congrArg Prod.snd (exteriorProductCochainEquiv_d d a q z)

/-- 概要：Koszul 外積模型の生成元追加はスカラー作用の mappingCone と同型。
方針：各整数次数の同型を微分比較で複体同型へまとめる。
規約：KST Def3.1、任意可換環上で非正則列も許す。
使われ方：既存 koszulComplex との有限列に関する帰納比較。 -/
def exteriorProductConeIso (d : M →ₗ[R] R) (a : R) :
    exteriorKoszulCochain (exteriorProductDifferential d a) ≅ exteriorScalarCone d a :=
  HomologicalComplex.Hom.isoOfComponents (exteriorToConeXIso d a) (by
    intro q j hqj
    obtain rfl : j = q + 1 := hqj.symm
    exact (exteriorToConeXIso_comm d a q).symm)

end SerrePositivity.KST.DerivedBlowup
