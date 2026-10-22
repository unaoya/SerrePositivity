module
public import SerrePositivity.KST.SConstruction.PointedPushoutLocalizedMono
public import SerrePositivity.KST.SConstruction.PointedTensorMappingCylinderWeakEquivalence
public import SerrePositivity.KST.SConstruction.PointedTensorMappingCylinderMono

/-! # 同じ実写像円柱を貼り付けた押し出しの弱比較
概要：左脚が局所化可逆なら、元の右標的から実円柱押し出しへの包含も局所化可逆。
方針：同じ円柱源射の単射性・局所化可逆性と実押し出しの保存定理を使う。
規約：右脚の単射性は不要。使われ方：関手的 BF 段と元の組み立ての比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open SerrePositivity.SimplicialModel

/-- 同じ元の写像円柱の源比較は、局所化で元の射と標的包含の合成になる。 -/
lemma pointedTensorMappingCylinderSource_localized_eq
    {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : anodyneExtensions.IsInvertedBy L)
    {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    L.map (pointedTensorMappingCylinderSource f).right =
      L.map f.right ≫ L.map (pointedTensorMappingCylinderTarget f).right := by
  let _ := pointedTensorMappingCylinderProjection_localized_isIso L hL f
  apply (cancel_mono (L.map (pointedTensorMappingCylinderProjection f).right)).mp
  have hs := congrArg (fun q => L.map q.right)
    (pointedTensorMappingCylinderSource_projection f)
  have ht := congrArg (fun q => L.map q.right)
    (pointedTensorMappingCylinderTarget_projection f)
  simp only [Under.comp_right, Under.id_right, L.map_comp, L.map_id] at hs ht
  rw [hs, Category.assoc, ht, Category.comp_id]

/-- 同じ実円柱押し出しの元の右包含は、左脚の局所化可逆性から局所化可逆。 -/
lemma pointedDoubleMappingCylinderRight_localized_isIso
    {X A B : PointedSimplicialSet.{u}} (f : X ⟶ A) (g : X ⟶ B)
    [IsIso (AnodyneHomotopy.anodyneQ.map f.right)] :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (pushout.inr (pointedTensorMappingCylinderSource f) g).right) := by
  exact pointedPushout_inr_localized_isIso _ g
    (pointedTensorMappingCylinderSource_localized_isIso AnodyneHomotopy.anodyneQ
      (Localization.inverts _ anodyneExtensions) f)

/-- 元の二脚と実円柱押し出しの両標的比較は、局所化で可換な四角形をなす。 -/
lemma pointedDoubleMappingCylinder_localized_square
    {X A B : PointedSimplicialSet.{u}} (f : X ⟶ A) (g : X ⟶ B) :
    AnodyneHomotopy.anodyneQ.map f.right ≫
        AnodyneHomotopy.anodyneQ.map
          (pointedTensorMappingCylinderTarget f ≫
            pushout.inl (pointedTensorMappingCylinderSource f) g).right =
      AnodyneHomotopy.anodyneQ.map g.right ≫
        AnodyneHomotopy.anodyneQ.map
          (pushout.inr (pointedTensorMappingCylinderSource f) g).right := by
  have h := congrArg (fun q => AnodyneHomotopy.anodyneQ.map q.right)
    (pushout.condition (f := pointedTensorMappingCylinderSource f) (g := g))
  simp only [Under.comp_right, CategoryTheory.Functor.map_comp] at h ⊢
  rw [← Category.assoc, ← pointedTensorMappingCylinderSource_localized_eq
    AnodyneHomotopy.anodyneQ (Localization.inverts _ anodyneExtensions)]
  exact h

end SerrePositivity.KST.SConstruction
