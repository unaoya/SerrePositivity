module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.HomotopyIntervalNaturality
/-!
概要：指定複体同型による同じ線形Homの始域の移送。
方針：既存コチェイン前合成に同じ両逆射を入れ、各次数で逆則を確認する。
規約：IS-W2 A12の前提計算2/3。元の前合成射と同型を保持する。
使われ方：HA 1.2.4、元のBK係数重み同型をΓ Homへ移す入口。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory HomologicalComplex CochainComplex HomComplex
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]
variable {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
/-- 元の指定複体同型の逆射による前合成を順射とするHom同型。 -/
def linearHomSourceIso {P P' : CochainComplex C ℤ} (e : P ≅ P') (Q : CochainComplex C ℤ) :
    linearHomComplex A P Q ≅ linearHomComplex A P' Q where
  hom := intervalHomPrePost A e.inv (𝟙 Q)
  inv := intervalHomPrePost A e.hom (𝟙 Q)
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Cochain.ext
    intro p q hpq
    change ((Cochain.ofHom e.hom).comp
      (((Cochain.ofHom e.inv).comp (z.comp (Cochain.ofHom (𝟙 Q)) (add_zero n))
        (zero_add n)).comp (Cochain.ofHom (𝟙 Q)) (add_zero n)) (zero_add n)).v p q hpq = z.v p q hpq
    simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      HomologicalComplex.id_f, Category.comp_id]
    rw [← Category.assoc, ← HomologicalComplex.comp_f, e.hom_inv_id,
      HomologicalComplex.id_f, Category.id_comp]
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Cochain.ext
    intro p q hpq
    change ((Cochain.ofHom e.inv).comp
      (((Cochain.ofHom e.hom).comp (z.comp (Cochain.ofHom (𝟙 Q)) (add_zero n))
        (zero_add n)).comp (Cochain.ofHom (𝟙 Q)) (add_zero n)) (zero_add n)).v p q hpq = z.v p q hpq
    simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      HomologicalComplex.id_f, Category.comp_id]
    rw [← Category.assoc, ← HomologicalComplex.comp_f, e.inv_hom_id,
      HomologicalComplex.id_f, Category.id_comp]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
