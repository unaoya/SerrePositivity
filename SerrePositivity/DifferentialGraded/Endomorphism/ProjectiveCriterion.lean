module
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveLocalizationHom
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveResolution
public import SerrePositivity.DifferentialGraded.Module.Precomposition

/-! # 主KにおけるHom計算によるホモトピー射影性の判定

指定射影解像度のK内retractを使う。新たな生成定理や引用を仮定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- K内で射影的加群のretractになる実際のdg加群もホモトピー射影的。 -/
lemma moduleHomotopicallyProjective_of_homotopyRetract
    {P Q : ModuleCategory A D} (i : P ⟶ Q) (r : Q ⟶ P)
    (h : (moduleToHomotopy A D).map (i ≫ r) = (moduleToHomotopy A D).map (𝟙 P))
    (hQ : moduleHomotopicallyProjective A D Q) : moduleHomotopicallyProjective A D P := by
  intro T hT q
  apply (exactAt_iff_isZero_homology _ q).2
  have hz := (hQ T hT q).isZero_homology
  obtain ⟨hh⟩ := (moduleToHomotopy_map_eq_iff A D (i ≫ r) (𝟙 P)).mp h
  have he := (moduleHomPrecomposeHomotopy A D hh T).homologyMap_eq q
  simp only [eHomWhiskerRight_comp, eHomWhiskerRight_id, homologyMap_comp, homologyMap_id] at he
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 (homology (P ⟶[Complex A] T) q) = 0
  change IsZero (homology (Q ⟶[Complex A] T) q) at hz
  rw [← he, hz.eq_of_tgt (homologyMap (eHomWhiskerRight (Complex A) r T) q) 0, zero_comp]

/-- KのHom(P,−)が指定擬同型を反転すれば、指定解像度がK内で分裂しPは射影的。 -/
lemma moduleHomotopicallyProjective_of_coyoneda_inverts (P : ModuleCategory A D)
    (hP : (moduleHomotopyQuasiIso A D).IsInvertedBy
      (coyoneda.obj (op ((moduleToHomotopy A D).obj P)))) :
    moduleHomotopicallyProjective A D P := by
  let R := moduleCanonicalProjectiveResolution A D P
  have hW := (moduleHomotopyQuasiIso_map_iff A D R.π).mpr R.quasiIso
  have hi := hP ((moduleToHomotopy A D).map R.π) hW
  have hb := (CategoryTheory.isIso_iff_bijective _).mp hi
  obtain ⟨s, hs⟩ := hb.2 (𝟙 ((moduleToHomotopy A D).obj P))
  obtain ⟨i, hi⟩ := (moduleToHomotopy A D).map_surjective s
  apply moduleHomotopicallyProjective_of_homotopyRetract A D i R.π _ R.projective
  rw [CategoryTheory.Functor.map_comp, hi, CategoryTheory.Functor.map_id]
  exact hs

/-- 主K上のcoyonedaによるホモトピー射影性の同値な判定。 -/
lemma moduleHomotopicallyProjective_iff_coyoneda_inverts (P : ModuleCategory A D) :
    moduleHomotopicallyProjective A D P ↔
      (moduleHomotopyQuasiIso A D).IsInvertedBy
        (coyoneda.obj (op ((moduleToHomotopy A D).obj P))) :=
  ⟨moduleHomotopicallyProjective_coyoneda_inverts A D,
    moduleHomotopicallyProjective_of_coyoneda_inverts A D P⟩

end SerrePositivity.DifferentialGraded
