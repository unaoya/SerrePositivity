module
public import SerrePositivity.KST.SConstruction.DGConeLiftModuleNaturality

/-!
概要：元二成分から同じ実 cone への全厳密 dg 比較を構成する。
方針：指定された閉条件と全次数自然性を同じ元 cone lift へ渡す。
規約：元次数一成分・次数零成分を保持する。
使われ方：元回転比較を全関手族として構成する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P]
  (F G H : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "a" => dgModuleNaturalConeArrow R D F G η
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
variable (h₁ : ∀ x, (moduleHom R D (H.obj x) (F.obj x)).X 1)
  (h₀ : ∀ x, (moduleHom R D (H.obj x) (G.obj x)).X 0)
  (c₁ : ∀ x, (moduleHom R D (H.obj x) (F.obj x)).d 1 2 (h₁ x) = 0)
variable (c₀ : ∀ x, (moduleHom R D (H.obj x) (G.obj x)).d 0 1 (h₀ x) +
    (show (moduleHom R D (H.obj x) (G.obj x)).X 1 from
      (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (H.obj x))
        (dgModuleNaturalConeArrow R D F G η x)).f 1 (h₁ x)) = 0)

/-- 概要：同じ指定二成分から同じ元実 cone へ入る閉射。
方針：既存の元 lift と指定閉条件を使用する。
規約：実 cone を選び直さない。使われ方：全厳密比較の元成分。 -/
def dgModuleNaturalConeLiftMap (x : P) :
    ForgetEnrichment.of (Complex R) (H.obj x) ⟶
      ForgetEnrichment.of (Complex R) ((CF).obj x) :=
  moduleConeLiftOfCycle R D (a x) (h₁ x) (h₀ x) (c₁ x) (c₀ x)

/-- 概要：同じ実 lift の閉元は元二成分からの指定 lift 元。
方針：元閉元・閉射対応の逆律を用いる。
規約：元比較成分を保持。使われ方：全 Hom の自然性の計算。 -/
lemma dgModuleNaturalConeLiftMap_cycle (x : P) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgModuleNaturalConeLiftMap R D F G H η h₁ h₀ c₁ c₀ x))).val =
      moduleConeLiftElement R D (T := ForgetEnrichment.of (Complex R) (H.obj x))
        (a x) 0 (h₁ x) (h₀ x) :=
  moduleMorphismOfCycle_cycle R D _ _

variable (n₁ : ∀ x y (n : ℤ) (z : GradedHom R x y n),
    compose R (x := H.obj x) (y := F.obj x) (z := F.obj y)
      ((F.map x y).f n z) (h₁ x) (add_comm 1 n) =
    n.negOnePow • compose R (x := H.obj x) (y := H.obj y) (z := F.obj y)
      (h₁ y) ((H.map x y).f n z) rfl)
  (n₀ : ∀ x y (n : ℤ) (z : GradedHom R x y n),
    compose R (x := H.obj x) (y := G.obj x) (z := G.obj y)
      ((G.map x y).f n z) (h₀ x) (zero_add n) =
    compose R (x := H.obj x) (y := H.obj y) (z := G.obj y)
      (h₀ y) ((H.map x y).f n z) (add_zero n))
include n₁ n₀

/-- 概要：元二成分の全自然性は同じ実 cone lift の全自然性を与える。
方針：同じ元実 Hom end の二射影検出を使う。
規約：元の全次数を保持。使われ方：全厳密回転比較への束ね。 -/
lemma dgModuleNaturalConeLiftMap_naturality (x y : P) (n : ℤ)
    (z : GradedHom R x y n) :
    compose R (x := H.obj x) (y := (CF).obj x) (z := (CF).obj y)
      (((CF).map x y).f n z)
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgModuleNaturalConeLiftMap R D F G H η h₁ h₀ c₁ c₀ x))).val (zero_add n) =
    compose R (x := H.obj x) (y := H.obj y) (z := (CF).obj y)
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgModuleNaturalConeLiftMap R D F G H η h₁ h₀ c₁ c₀ y))).val
      ((H.map x y).f n z) (add_zero n) := by
  rw [dgModuleNaturalConeLiftMap_cycle, dgModuleNaturalConeLiftMap_cycle]
  exact dgConeLiftModule_naturality R D (a x) (a y)
    ((F.map x y).f n z) ((G.map x y).f n z) ((H.map x y).f n z)
    (h₁ x) (h₁ y) (h₀ x) (h₀ y) (n₁ x y n z) (n₀ x y n z)

/-- 概要：指定二成分と閉条件から得られる同じ元 cone への全厳密 dg 比較。
方針：元閉射と証明済み全 Hom 自然性を束ねる。
規約：点ごとの比較射の存在選択をしない。
使われ方：実回転比較の全関手族化。 -/
def dgModuleNaturalConeLift : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans H (CF) where
  app x := cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
    (dgModuleNaturalConeLiftMap R D F G H η h₁ h₀ c₁ c₀ x))
  naturality z := (dgModuleNaturalConeLiftMap_naturality R D F G H η h₁ h₀ c₁ c₀ n₁ n₀ _ _ _ z).symm
end SerrePositivity.KST.SConstruction
