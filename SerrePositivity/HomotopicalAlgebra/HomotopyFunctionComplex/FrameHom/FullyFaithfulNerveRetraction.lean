module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage

/-!
# 充満忠実な包含の自然な片側収縮から nerve の反転性

概要：充満忠実な包含が自然な単位または余単位を持つ戻しを持てば nerve を反転。
方針：包含先の自然変換を充満忠実性で包含元へ戻し、同じ二つのホモトピーを使う。
規約：随伴の三角恒等式や単体集合モデルは仮定しない。
使われ方：三本矢の各片脚の関手的置換による包含の反転性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FullyFaithfulNerveRetraction
open _root_.SerrePositivity.SimplicialModel

variable {A B : Type u} [Category.{v} A] [Category.{v} B]
  (I : A ⥤ B) [I.Full] [I.Faithful] (R : B ⥤ A)

/-- 元の包含先の単位を、包含元の全対象・全射へ戻す。 -/
def liftUnit (η : 𝟭 B ⟶ R ⋙ I) : 𝟭 A ⟶ I ⋙ R where
  app a := I.preimage (η.app (I.obj a))
  naturality a b f := by
    apply I.map_injective
    simpa only [I.map_comp, I.map_preimage, Functor.id_map, Functor.comp_map] using
      η.naturality (I.map f)

/-- 元の包含先の余単位も、包含元の全対象・全射へ戻す。 -/
def liftCounit (ε : R ⋙ I ⟶ 𝟭 B) : I ⋙ R ⟶ 𝟭 A where
  app a := I.preimage (ε.app (I.obj a))
  naturality a b f := by
    apply I.map_injective
    simpa only [I.map_comp, I.map_preimage, Functor.id_map, Functor.comp_map] using
      ε.naturality (I.map f)

/-- 元の自然な単位があれば、同じ包含の nerve そのものを局所化で反転できる。 -/
lemma of_unit (η : 𝟭 B ⟶ R ⋙ I) :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap I)) := by
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  let e : Q.obj (nerve A) ≅ Q.obj (nerve B) :=
    { hom := Q.map (nerveMap I)
      inv := Q.map (nerveMap R)
      hom_inv_id := by
        have h := AnodyneHomotopy.map_homotopy_eq Q
          (Localization.inverts _ SSet.anodyneExtensions)
          (_root_.SerrePositivity.NerveHomotopy.homotopy (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FullyFaithfulNerveRetraction.liftUnit I R η))
        change Q.map (𝟙 _) = Q.map (nerveMap I ≫ nerveMap R) at h
        rw [Q.map_comp, Q.map_id] at h
        exact h.symm
      inv_hom_id := by
        have h := AnodyneHomotopy.map_homotopy_eq Q
          (Localization.inverts _ SSet.anodyneExtensions) (_root_.SerrePositivity.NerveHomotopy.homotopy η)
        change Q.map (𝟙 _) = Q.map (nerveMap R ≫ nerveMap I) at h
        rw [Q.map_comp, Q.map_id] at h
        exact h.symm }
  exact e.isIso_hom

/-- 元の自然な余単位の場合も、同じ包含の nerve を局所化で反転できる。 -/
lemma of_counit (ε : R ⋙ I ⟶ 𝟭 B) :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap I)) := by
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  let e : Q.obj (nerve A) ≅ Q.obj (nerve B) :=
    { hom := Q.map (nerveMap I)
      inv := Q.map (nerveMap R)
      hom_inv_id := by
        have h := AnodyneHomotopy.map_homotopy_eq Q
          (Localization.inverts _ SSet.anodyneExtensions)
          (_root_.SerrePositivity.NerveHomotopy.homotopy (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FullyFaithfulNerveRetraction.liftCounit I R ε))
        change Q.map (nerveMap I ≫ nerveMap R) = Q.map (𝟙 _) at h
        rw [Q.map_comp, Q.map_id] at h
        exact h
      inv_hom_id := by
        have h := AnodyneHomotopy.map_homotopy_eq Q
          (Localization.inverts _ SSet.anodyneExtensions) (_root_.SerrePositivity.NerveHomotopy.homotopy ε)
        change Q.map (nerveMap R ≫ nerveMap I) = Q.map (𝟙 _) at h
        rw [Q.map_comp, Q.map_id] at h
        exact h }
  exact e.isIso_hom

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FullyFaithfulNerveRetraction
