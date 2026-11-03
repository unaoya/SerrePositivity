module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.Cone
public import SerrePositivity.InfinityCategories.Core.UniverseLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeSimplex
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanConeLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseCosliceUncurry
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinFunctor
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.WithInitialKanCone
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeReindex

/-!
概要：通常の錐の nerve の持ち上げと、Kan 値 strict coherent 錐を全錐で比較する。
方針：join の左頂点と右因子の全標準単体で元の錐の射列を照合する。
規約：源の nerve と join の宇宙比較を含み、頂点と脚だけで代用しない。
使われ方：Sp β6 f4d の通常の錐からの native な全錐の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：通常の nerve 錐は添字の制限と全写像として可換。
方針：WithInitial の join 比較の自然性と、拡張錐関手の厳密な制限を使う。
規約：添字の圏に thin 性を要求しない。
使われ方：全標準単体での比較を小さい有限順序圏へ縮約する。 -/
lemma nerveCone_whisker_val {I J C : Type u}
    [SmallCategory I] [SmallCategory J] [SmallCategory C]
    {F : I ⥤ C} (c : Cone F) (G : J ⥤ I) :
    joinMap (𝟙 Δ[0]) (nerveMap G) ≫ (F1B.nerveCone c).val =
      (F1B.nerveCone (c.whisker G)).val := by
  change joinMap (𝟙 Δ[0]) (nerveMap G) ≫
    (initialJoinNerveMap I ≫ nerveMap (F1B.coneWithInitialFunctor c)) =
    initialJoinNerveMap J ≫ nerveMap (F1B.coneWithInitialFunctor (c.whisker G))
  rw [← Category.assoc, initialJoinNerveMap_naturality, Category.assoc]
  change initialJoinNerveMap J ≫
    nerveMap (WithInitial.map G ⋙ F1B.coneWithInitialFunctor c) = _
  congr 2
  refine CategoryTheory.Functor.ext (fun x ↦ by cases x <;> rfl) ?_
  rintro (x | _) (y | _) f
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · exact PEmpty.elim (show PEmpty from f)
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- 概要：錐形状の宇宙比較は右因子の任意の写像と厳密に可換。
方針：join の宇宙比較の自然性と標準零単体の比較を合成する。
規約：全次数の写像を比較する。
使われ方：持ち上げた nerve 錐の再添字。 -/
lemma uliftConeShapeIso_inv_right {I J : SSet.{u}} (f : J ⟶ I) :
    joinMap (𝟙 (Δ[0] : SSet.{u + 1})) ((SSet.uliftFunctor.{u + 1, u}).map f) ≫
      (uliftConeShapeIso I 0).inv =
    (uliftConeShapeIso J 0).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (joinMap (𝟙 (Δ[0] : SSet.{u})) f) := by
  dsimp only [uliftConeShapeIso, Iso.trans_inv, joinIso, Iso.refl_inv]
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id]
  have h := uliftJoinIso_inv_naturality.{u, u + 1} (𝟙 (Δ[0] : SSet.{u})) f
  simp only [CategoryTheory.Functor.map_id] at h
  rw [Category.assoc, ← h, ← Category.assoc, ← joinMap_comp,
    Category.comp_id, Category.id_comp]

/-- 概要：持ち上げた通常の nerve 錐も添字の制限と全写像として可換。
方針：元の再添字の等式を錐形状の宇宙比較の自然性で持ち上げる。
規約：元の全錐を変更しない。
使われ方：全標準単体での比較の有限順序圏への縮約。 -/
lemma uliftNerveCone_whisker_val {I J C : Type u}
    [SmallCategory I] [SmallCategory J] [SmallCategory C]
    {F : I ⥤ C} (c : Cone F) (G : J ⥤ I) :
    joinMap (𝟙 Δ[0]) ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap G)) ≫
      (JoinCone.ulift.{u, u + 1} (F1B.nerveCone c)).val =
      (JoinCone.ulift.{u, u + 1} (F1B.nerveCone (c.whisker G))).val := by
  change _ ≫ ((uliftConeShapeIso (nerve I) 0).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map (F1B.nerveCone c).val) =
    (uliftConeShapeIso (nerve J) 0).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (F1B.nerveCone (c.whisker G)).val
  rw [← Category.assoc, uliftConeShapeIso_inv_right, Category.assoc,
    ← Functor.map_comp, nerveCone_whisker_val]

/-- 概要：通常の錐の持ち上げ後の像は始対象付き関手の全 coherent 図式。
方針：錐形状の逆同型と nerve の合成を正規化する。
規約：元の全写像の等式である。
使われ方：既存の始対象付き Kan 図式の比較への接続。 -/
lemma uliftNerveCone_image_eq_initial {I C : Type u} [SmallCategory I] [SmallCategory C]
    {F : I ⥤ C} (c : Cone F) (H : C ⥤ KanObject.{u}) :
    (JoinCone.ulift.{u, u + 1} (F1B.nerveCone c)).val ≫ kanDiagramCoherentNerve H =
      (F2.Presentable.uliftInitialConeIso I).inv ≫
        kanDiagramCoherentNerve (F1B.coneWithInitialFunctor c ⋙ H) := by
  change ((uliftConeShapeIso (nerve I) 0).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (initialJoinNerveMap I ≫ nerveMap (F1B.coneWithInitialFunctor c))) ≫ _ =
    ((uliftConeShapeIso (nerve I) 0).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (initialJoinNerveMap I)) ≫ _
  rw [Functor.map_comp]
  simp only [Category.assoc]
  congr 2

/-- 概要：thin な添字では nerve 錐の宇宙持ち上げの像と strict coherent 錐は全体で一致。
方針：始対象付き関手の全図式比較に元の拡張錐関手を代入する。
規約：標的 C には thin 性を要求しない。
使われ方：一般の添字の全標準単体による検証の有限順序圏の場合。 -/
lemma uliftNerveCone_coherent_eq_of_thin {I C : Type u}
    [SmallCategory I] [Quiver.IsThin I] [SmallCategory C]
    {F : I ⥤ C} (c : Cone F) (H : C ⥤ KanObject.{u}) :
    (JoinCone.ulift.{u, u + 1} (F1B.nerveCone c)).val ≫ kanDiagramCoherentNerve H =
      (strictCoherentCone (H.mapCone c)).val := by
  rw [uliftNerveCone_image_eq_initial]
  exact F2.Presentable.withInitialKanCone_coherentMap (F1B.coneWithInitialFunctor c ⋙ H)

/-- 概要：通常の錐の nerve の宇宙持ち上げ後の像は strict coherent 錐と全体で一致。
方針：左頂点と右因子の全標準単体で比較し、各単体を有限順序圏へ制限する。
規約：添字と標的に thin 性を要求せず、全錐の高次資料を保持する。
使われ方：Sp β6 f4d の通常の錐と native な Kan 値錐の同定。 -/
lemma uliftNerveCone_coherent_eq {I C : Type u} [SmallCategory I] [SmallCategory C]
    {F : I ⥤ C} (c : Cone F) (H : C ⥤ KanObject.{u}) :
    (JoinCone.ulift.{u, u + 1} (F1B.nerveCone c)).val ≫ kanDiagramCoherentNerve H =
      (strictCoherentCone (H.mapCone c)).val := by
  change (JoinCone.ulift.{u, u + 1} (F1B.nerveCone c)).val ≫
    kanDiagramCoherentNerve H = strictCoherentConeMap (H.mapCone c)
  apply join_right_hom_ext
  · rw [strictCoherentConeMap_inl]
    apply SSet.yonedaEquiv.injective
    erw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change (kanDiagramCoherentNerve H).app (Opposite.op ⦋0⦌)
      (JoinCone.ulift.{u, u + 1} (F1B.nerveCone c)).vertex = _
    rw [JoinCone.ulift_vertex, F1B.nerveCone_vertex]
    exact (kanDiagramCoherentNerve_vertex H c.pt).trans
      (spaceInfinityVertex_eq_coherent _)
  · intro n a
    let T : ULift.{u} (Fin (n + 1)) ⥤ I :=
      (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙
        (SSet.yonedaEquiv a).down
    let b : (Δ[n] : SSet.{u + 1}) ⟶
        (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} (Fin (n + 1)))) :=
      SSet.yonedaEquiv.symm (ULift.up
        (⟨ULift.up, fun _ _ h ↦ h⟩ : Fin (n + 1) →o ULift.{u} (Fin (n + 1))).toFunctor)
    let j := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap T)
    have hab : b ≫ j = a := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      change ULift.up
        ((⟨ULift.up, fun _ _ h ↦ h⟩ : Fin (n + 1) →o ULift.{u} (Fin (n + 1))).toFunctor ⋙ T) =
          SSet.yonedaEquiv a
      rfl
    have hjm : joinMap (𝟙 (Δ[0] : SSet.{u + 1})) a =
        joinMap (𝟙 Δ[0]) b ≫ joinMap (𝟙 Δ[0]) j := by
      rw [← joinMap_comp, Category.id_comp, hab]
    rw [hjm, Category.assoc, ← Category.assoc (joinMap (𝟙 Δ[0]) j),
      uliftNerveCone_whisker_val, Category.assoc,
      uliftNerveCone_coherent_eq_of_thin]
    change joinMap (𝟙 Δ[0]) b ≫ strictCoherentConeMap (H.mapCone (c.whisker T)) =
      (joinMap (𝟙 Δ[0]) b ≫ joinMap (𝟙 Δ[0])
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap T))) ≫ strictCoherentConeMap (H.mapCone c)
    rw [Category.assoc, strictCoherentConeMap_whisker]
    rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
