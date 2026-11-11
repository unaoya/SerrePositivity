module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices

/-!
概要：通常の順序図式を coherent nerve の豊穣図式として表す。
方針：path の端点が定める順序射を写し、豊穣 Hom では対応する頂点に定値とする。
規約：この構成は strict diagram の表示であり、一般の coherent diagram の分類は主張しない。
使われ方：Kerodon §2.4.3（Tag 00KM）、Remark 3.1.6.3（Tag 01YZ）、pointed space の fiber への比較射の準備。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：単位からの射の各成分は対応する零単体の定値単体。
方針：単位からの射と零単体の同値の逆の成分を計算する。
規約：単体集合 X は任意。
使われ方：Kerodon §2.4.3（Tag 00KM）、定値な豊穣 Hom の単位則。 -/
lemma unitHom_app_constant {X : SSet.{u}} (f : (𝟙_ SSet.{u}) ⟶ X) (n : ℕ) :
    f.app (Opposite.op ⦋n⦌) PUnit.unit = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SSet.unitHomEquiv X f) n := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app ((SSet.unitHomEquiv X).symm_apply_apply f) (Opposite.op ⦋n⦌)) PUnit.unit
  exact h.symm

/-- 概要：通常の射の合成は豊穣 Hom の零単体の合成に一致する。
方針：通常の圏と豊穣圏の整合性を零単体で評価する。
規約：任意の単体的圏を扱う。
使われ方：Kerodon §2.4.3（Tag 00KM）、strict な図式の coherent な表示。 -/
lemma simplicialHom_vertex_comp {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) :
    SimplicialCategory.homEquiv' A D (f ≫ g) =
      (SimplicialCategory.sHomComp A B D).app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' A B f, SimplicialCategory.homEquiv' B D g) :=
  congrArg (SSet.unitHomEquiv _) (eHomEquiv_comp SSet f g)

/-- 概要：通常の射を表す定値単体の豊穣合成は合成射の定値単体。
方針：合成の自然性と零単体での計算を使う。
規約：単体の次数 n は任意。
使われ方：Kerodon §2.4.3（Tag 00KM）、順序図式の豊穣関手の合成則。 -/
lemma simplicialHom_constant_comp {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (n : ℕ) :
    (SimplicialCategory.sHomComp A B D).app (Opposite.op ⦋n⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' A B f) n,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' B D g) n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' A D (f ≫ g)) n := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map (SimplicialCategory.sHomComp A B D)
    (SimplicialCategory.homEquiv' A B f, SimplicialCategory.homEquiv' B D g) n
  rw [← simplicialHom_vertex_comp] at h
  exact h

/-- 概要：順序図式の二端点の間の豊穣 Hom の射。
方針：path の存在から端点の順序射を取り、その像の定値単体を使う。
規約：path の途中の点の選び方には依存しない。
使われ方：Kerodon §2.4.3（Tag 00KM）、通常の射を coherent nerve の辺にする構成。 -/
noncomputable def orderDiagramEnrichedHom {J : Type u} [LinearOrder J]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (F : J ⥤ C)
    (i j : SimplicialThickening J) :
    SimplicialCategory.sHom i j ⟶ SimplicialCategory.sHom (F.obj i.as) (F.obj j.as) where
  app n := ↾fun P ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
    (SimplicialCategory.homEquiv' _ _ (F.map (homOfLE
      (SimplicialThickening.Path.le (P.obj 0))))) n.unop.len
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro P
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback
      (SimplicialCategory.homEquiv' _ _
        (F.map (homOfLE (SimplicialThickening.Path.le (P.obj 0))))) α.unop).symm

/-- 概要：通常の順序図式は simplicial thickening からの豊穣関手を与える。
方針：端点間の順序射の像を定値な豊穣 Hom とし、通常の関手則を使う。
規約：途中の path の情報を捨てた strict な coherent 表示。
使われ方：Kerodon §2.4.3（Tag 00KM）、Remark 3.1.6.3（Tag 01YZ）、pointed space の比較射の辺。 -/
noncomputable def enrichedFunctorOfOrderDiagram {J : Type u} [LinearOrder J]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (F : J ⥤ C) :
    EnrichedFunctor SSet (SimplicialThickening J) C where
  obj i := F.obj i.as
  map := orderDiagramEnrichedHom F
  map_id i := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (F.map (𝟙 i.as))) n =
      (eId SSet (F.obj i.as)).app (Opposite.op ⦋n⦌) s
    rw [F.map_id]
    have hs : s = PUnit.unit := by exact @Subsingleton.elim PUnit inferInstance _ _
    subst s
    simpa only [SimplicialCategory.homEquiv', Equiv.trans_apply, eHomEquiv_id]
      using (unitHom_app_constant (eId SSet (F.obj i.as)) n).symm
  map_comp i j k := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _
      (F.map (homOfLE ((SimplicialThickening.Path.le (P.obj 0)).trans
        (SimplicialThickening.Path.le (Q.obj 0)))))) n =
        (SimplicialCategory.sHomComp _ _ _).app (Opposite.op ⦋n⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _
            (F.map (homOfLE (SimplicialThickening.Path.le (P.obj 0))))) n,
           _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _
            (F.map (homOfLE (SimplicialThickening.Path.le (Q.obj 0))))) n)
    rw [simplicialHom_constant_comp, ← F.map_comp]
    rfl

/-- 概要：順序図式の coherent 表示は単調写像による前合成と可換。
方針：豊穣関手の対象と定値な Hom の作用を比較する。
規約：両方の順序集合は宇宙 u に属する。
使われ方：Kerodon §2.4.3（Tag 00KM）、通常の nerve から coherent nerve への射の自然性。 -/
lemma enrichedFunctorOfOrderDiagram_precomp {J K : Type u} [LinearOrder J] [LinearOrder K]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (α : J →o K) (F : K ⥤ C) :
    (SimplicialThickening.functor α).comp SSet (enrichedFunctorOfOrderDiagram F) =
      enrichedFunctorOfOrderDiagram (α.toFunctor ⋙ F) := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro i j
  simp only [eqToHom_refl, Category.comp_id]

/-- 概要：単体的圏の通常の nerve から coherent nerve への標準射。
方針：通常の各順序図式を定値な豊穣 Hom の図式として表す。
規約：通常の射の合成をそのまま coherent な単体にする。
使われ方：Kerodon §2.4.3（Tag 00KM）、Remark 3.1.6.3（Tag 01YZ）、通常の射から coherent nerve の辺を作る。 -/
noncomputable def nerveToCoherent (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    nerve C ⟶ SimplicialNerve C where
  app n := ↾fun F ↦ enrichedFunctorOfOrderDiagram
    ((⟨ULift.down, fun _ _ h ↦ h⟩ :
      ULift.{u} (Fin (n.unop.len + 1)) →o Fin (n.unop.len + 1)).toFunctor ⋙ F)
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro F
    change enrichedFunctorOfOrderDiagram _ =
      (SimplicialThickening.functor α.unop.toOrderHom.uliftMap).comp SSet
        (enrichedFunctorOfOrderDiagram ((⟨ULift.down, fun _ _ h ↦ h⟩ :
      ULift.{u} (Fin (n.unop.len + 1)) →o Fin (n.unop.len + 1)).toFunctor ⋙ F))
    rw [enrichedFunctorOfOrderDiagram_precomp]
    rfl

/-- 概要：通常の nerve の頂点は coherent nerve の同じ対象の頂点に写る。
方針：coherent nerve の零単体が対象から復元できることを使う。
規約：通常の nerve の頂点は ComposableArrows.mk₀ で表す。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、標準射の始点と終点の照合。 -/
lemma nerveToCoherent_vertex {C : Type v} [Category.{u} C] [SimplicialCategory C] (X : C) :
    (nerveToCoherent C).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object
    ((nerveToCoherent C).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X))).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
