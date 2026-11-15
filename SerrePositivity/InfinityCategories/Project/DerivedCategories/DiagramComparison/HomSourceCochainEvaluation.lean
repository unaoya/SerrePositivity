module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearHomSourceIso

/-!
概要：指定Hom始域移送の各次数を同じ閉零射の前合成で評価する。
方針：既存cochain合成成分則と恒等射則・結合則を使う。
規約：全斉次射と任意の線形加法圏。既存構成の評価・合成則。
使われ方：HA 1.2.4、IS-W2 B02の実際の係数重み移送の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]
variable {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]

/-- 標的を固定した指定Hom移送は同じ始域射のcochain前合成。 -/
theorem intervalHomPrePost_id_apply {P P' Q : CochainComplex C ℤ}
    (σ : P' ⟶ P) (p : ℤ) (z : Cochain P Q p) :
    (intervalHomPrePost A σ (𝟙 Q)).f p z =
      (Cochain.ofHom σ).comp z (zero_add p) := by
  apply Cochain.ext
  intro i j hij
  change ((Cochain.ofHom σ).comp
    (z.comp (Cochain.ofHom (𝟙 Q)) (add_zero p)) (zero_add p)).v i j hij = _
  simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, HomologicalComplex.id_f, Category.comp_id]

/-- 指定始域同型によるHom同型の順射も同じ逆射の前合成。 -/
theorem linearHomSourceIso_hom_apply {P P' : CochainComplex C ℤ}
    (e : P ≅ P') (Q : CochainComplex C ℤ) (p : ℤ) (z : Cochain P Q p) :
    (linearHomSourceIso A e Q).hom.f p z =
      (Cochain.ofHom e.inv).comp z (zero_add p) :=
  intervalHomPrePost_id_apply A e.inv p z

/-- 二つの閉零次始域射の前合成は同じ合成射の前合成。 -/
theorem zeroSourcePrecomp_comp {P P' P'' Q : CochainComplex C ℤ}
    (a : P'' ⟶ P') (b : P' ⟶ P) (p : ℤ) (z : Cochain P Q p) :
    (Cochain.ofHom a).comp ((Cochain.ofHom b).comp z (zero_add p)) (zero_add p) =
      (Cochain.ofHom (a ≫ b)).comp z (zero_add p) := by
  apply Cochain.ext
  intro i j hij
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    HomologicalComplex.comp_f, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
