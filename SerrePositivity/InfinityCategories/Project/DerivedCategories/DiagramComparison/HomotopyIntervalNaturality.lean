module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.HomotopyIntervalCochain
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalCochainNaturality
/-!
概要：同じホモトピーの内部Hom区間評価は前後合成に自然。
方針：零次閉射によるコチェイン合成と既存微分公式を使う。
規約：A06自然性の証明分割。元のホモトピーの前後合成を保持する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory HomologicalComplex CochainComplex HomComplex
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]
variable {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
/-- 前後の閉射を合成する、同じ内部Hom複体の指定射。 -/
def intervalHomPrePost {R R' S S' : CochainComplex C ℤ} (a : R' ⟶ R) (b : S ⟶ S') :
    linearHomComplex A R S ⟶ linearHomComplex A R' S' where
  f n := ModuleCat.ofHom
    { toFun z := (Cochain.ofHom a).comp (z.comp (Cochain.ofHom b) (add_zero n)) (zero_add n)
      map_add' z z' := by rw [Cochain.add_comp, Cochain.comp_add]
      map_smul' r z := by simp only [Cochain.smul_comp, Cochain.comp_smul, RingHom.id_apply] }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change δ n m ((Cochain.ofHom a).comp (z.comp (Cochain.ofHom b) (add_zero n)) (zero_add n)) =
      (Cochain.ofHom a).comp ((δ n m z).comp (Cochain.ofHom b) (add_zero m)) (zero_add m)
    rw [δ_ofHom_comp, δ_comp_ofHom]
/-- 閉零次射への同じ前後合成の値。 -/
theorem intervalHomPrePost_ofHom {R R' S S' : CochainComplex C ℤ}
    (a : R' ⟶ R) (b : S ⟶ S') (f : R ⟶ S) :
    (intervalHomPrePost A a b).f 0 (Cochain.ofHom f) = Cochain.ofHom (a ≫ f ≫ b) := by
  apply Cochain.ext₀
  intro i
  change ((Cochain.ofHom a).comp ((Cochain.ofHom f).comp (Cochain.ofHom b) (add_zero 0))
    (zero_add 0)).v i i (add_zero i) = _
  simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    HomologicalComplex.comp_f]
/-- ホモトピーの負一次値にも同じ前後合成を使う。 -/
theorem intervalHomPrePost_ofHomotopy {R R' S S' : CochainComplex C ℤ}
    (a : R' ⟶ R) (b : S ⟶ S') (f g : R ⟶ S) (h : Homotopy f g) :
    (intervalHomPrePost A a b).f (-1) (-Cochain.ofHomotopy h) =
      -Cochain.ofHomotopy ((h.compRight b).compLeft a) := by
  rw [map_neg]
  congr 1
  apply Cochain.ext
  intro p q hpq
  change ((Cochain.ofHom a).comp ((Cochain.ofHomotopy h).comp (Cochain.ofHom b) (add_zero (-1)))
    (zero_add (-1))).v p q hpq = _
  simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  change a.f p ≫ h.hom p q ≫ b.f q = a.f p ≫ h.hom p q ≫ b.f q
  rfl
/-- 同じ正規化区間の内部Hom評価は元の前後合成で可換になる。 -/
theorem homotopyIntervalCochainMap_naturality {R R' S S' : CochainComplex C ℤ}
    (a : R' ⟶ R) (b : S ⟶ S') (f g : R ⟶ S) (h : Homotopy f g) :
    homotopyIntervalCochainMap A f g h ≫ intervalHomPrePost A a b =
      homotopyIntervalCochainMap A (a ≫ f ≫ b) (a ≫ g ≫ b)
        ((h.compRight b).compLeft a) := by
  have hx := intervalHomPrePost_ofHom A a b f
  have hy := intervalHomPrePost_ofHom A a b g
  have hw := intervalHomPrePost_ofHomotopy A a b f g h
  dsimp only [homotopyIntervalCochainMap]
  have hq := normalizedIntervalCochainMapOfBoundary_postcomp A (intervalHomPrePost A a b)
    (Cochain.ofHom f) (Cochain.ofHom g) (δ_ofHom f) (δ_ofHom g) (-Cochain.ofHomotopy h)
    (by rw [map_neg]; change -δ (-1) 0 (Cochain.ofHomotopy h) = _; rw [δ_ofHomotopy, neg_sub])
    (by rw [hx]; exact δ_ofHom _)
    (by rw [hy]; exact δ_ofHom _)
    (by rw [hw, hx, hy]; rw [map_neg]; change -δ (-1) 0 (Cochain.ofHomotopy _) = _;
        rw [δ_ofHomotopy, neg_sub])
  simpa only [hx, hy, hw] using hq
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
