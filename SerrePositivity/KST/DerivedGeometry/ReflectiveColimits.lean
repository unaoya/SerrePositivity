module

public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# 層化を経由する余極限保存の判定

概要：反射的局所化の前に合成して余極限保存を確認する方法を証明する。
方針：反射関手で送った余極限余錐を、随伴の同型な余単位で移す。
規約：必要な余極限と合成の保存性を明記し、結論を仮定として束ねない。
使われ方：Toën Derived Azumaya §3.2、KST T1 の層化後の係数忘却。
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace SerrePositivity.KST.DerivedGeometry

/--
概要：反射関手との合成が指定形の余極限を保てば、元の関手も保つ。
方針：右随伴で戻した図式の余極限を反射し、余単位で元の図式へ移す。
規約：余単位は自然同型とし、反射前の圏に指定形の余極限があるとする。
使われ方：Toën §3.2、KST T1 の加群前層から加群層への余極限保存の移送。
-/
lemma preservesColimitsOfShape_of_reflective
    {C D E J : Type*} [Category C] [Category D] [Category E] [Category J]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R) [IsIso adj.counit]
    (F : D ⥤ E) [HasColimitsOfShape J C] [PreservesColimitsOfShape J (L ⋙ F)] :
    PreservesColimitsOfShape J F := by
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  refine ⟨fun {K} => ?_⟩
  have hc := colimit.isColimit (K ⋙ R)
  have : PreservesColimit ((K ⋙ R) ⋙ L) F :=
    preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves L hc)
      (isColimitOfPreserves (L ⋙ F) hc)
  exact preservesColimit_of_iso_diagram F
    (Functor.associator K R L ≪≫ Functor.isoWhiskerLeft K (asIso adj.counit) ≪≫
      Functor.rightUnitor K)

end SerrePositivity.KST.DerivedGeometry
