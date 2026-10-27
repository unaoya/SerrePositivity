module
public import SerrePositivity.KST.SConstruction.DGFunctorHomElements

/-!
概要：全次数で符号付き自然な斉次成分族を、同じ dg 関手 Hom end の元へ持ち上げる。
方針：各成分を disk の生成元の像とし、自然性を生成元で検査して end の普遍性を使う。
規約：閉零成分への限定なし。全 Hom 自然性を明示的に検査する。
使われ方：元 cone の指定零化元を全関手族の二単体へ接続する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] (F G : DGFunctor R D E) (q : ℤ)
  (z : ∀ x : D, GradedHom R (F.obj x) (G.obj x) q)
  (hz : ∀ (x y : D) (p n : ℤ) (f : GradedHom R x y p) (hn : q + p = n) (hn' : p + q = n),
    (q * p).negOnePow • forward R ((F.map x y).f p f) (z y) hn' =
      forward R (z x) ((G.map x y).f p f) hn)

include hz

/-- 概要：同じ斉次族の disk 表示は全豊穣 Hom に関して自然。
方針：転置した chain map を元生成元で判定する。
規約：全 Hom 次数と Koszul 符号を保持。使われ方：end 元の構成。 -/
lemma dgFunctorHomDiskFamily_naturality (x y : D) :
    (β_ (complexDisk R q) (x ⟶[Complex R] y)).hom ≫
      (F.map x y ⊗ₘ (complexDiskHomEquiv R _ q).symm (z y)) ≫
        eComp (Complex R) _ _ _ =
    ((complexDiskHomEquiv R _ q).symm (z x) ⊗ₘ G.map x y) ≫
      eComp (Complex R) _ _ _ := by
  have hc : curryRight ((β_ (complexDisk R q) (x ⟶[Complex R] y)).hom ≫
      (F.map x y ⊗ₘ (complexDiskHomEquiv R _ q).symm (z y)) ≫
        eComp (Complex R) _ _ _) =
    curryRight (((complexDiskHomEquiv R _ q).symm (z x) ⊗ₘ G.map x y) ≫
      eComp (Complex R) _ _ _) := by
    apply (complexDiskHomEquiv R _ q).injective
    rw [complexDiskHomEquiv_apply, complexDiskHomEquiv_apply]
    apply Cochain.ext
    intro p n hpn
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change (curryComponent _ q _).v p n hpn f = (curryComponent _ q _).v p n hpn f
    rw [curryComponent_apply, curryComponent_apply]
    change (eComp (Complex R) _ _ _).f n
        ((F.map x y ⊗ₘ (complexDiskHomEquiv R _ q).symm (z y)).f n
          ((signedSwap (complexDisk R q) (x ⟶[Complex R] y)).hom.f n
            (ιTensorObj (complexDisk R q) (x ⟶[Complex R] y) q p n (by omega)
              (((complexDiskX₀ R q).inv (1 : R)) ⊗ₜ[R] f)))) =
      (eComp (Complex R) _ _ _).f n
        (((complexDiskHomEquiv R _ q).symm (z x) ⊗ₘ G.map x y).f n
          (ιTensorObj (complexDisk R q) (x ⟶[Complex R] y) q p n (by omega)
            (((complexDiskX₀ R q).inv (1 : R)) ⊗ₜ[R] f)))
    rw [signedSwap_apply]
    simp only [Units.smul_def, map_zsmul]
    rw [tensorMap_apply, tensorMap_apply, complexDiskHomEquiv_symm_generator,
      complexDiskHomEquiv_symm_generator]
    exact hz x y p n f (by omega) hpn
  exact (uncurryRight_curryRight _).symm.trans
    ((congrArg uncurryRight hc).trans (uncurryRight_curryRight _))

/-- 概要：全 Hom に関して符号付き自然な同じ斉次族の end 内の実元。
方針：元 disk 全族を end へ持ち上げ、その生成元を読む。
規約：追加の自然性選択なし。使われ方：指定零化の全次数 Hom 表示。 -/
def dgFunctorHomElementFromFamily : (dgFunctorHom R D E F G).X q :=
  complexDiskHomEquiv R _ q ((dgFunctorHomEquiv R D E (complexDisk R q) F G).symm
    { app x := (complexDiskHomEquiv R _ q).symm (z x)
      naturality x y := dgFunctorHomDiskFamily_naturality R D E F G q z hz x y })

/-- 概要：持ち上げた同じ end 元の各対象評価は元成分そのもの。
方針：disk と end の二つの普遍性を合成する。
規約：全整数次数の厳密等号。使われ方：元指定微分境界の回収。 -/
lemma dgFunctorHomElementFromFamily_π (x : D) :
    (dgFunctorHomπ R D E F G x).f q
      (dgFunctorHomElementFromFamily R D E F G q z hz) = z x := by
  rw [dgFunctorHomElementFromFamily, ← complexDiskHomEquiv_naturality,
    dgFunctorHomEquiv_symm_π]
  exact (complexDiskHomEquiv R _ q).apply_symm_apply (z x)

end SerrePositivity.KST.SConstruction
