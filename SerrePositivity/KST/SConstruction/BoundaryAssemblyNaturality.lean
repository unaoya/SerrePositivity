module
public import SerrePositivity.KST.SConstruction.KanAssemblySequence
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-! # 境界商の段の接続のホモトピー自然性
概要：比較の逆射を使った境界商の随伴射も、入力の射についてホモトピー自然。
方針：逆射の自然性を写像空間の成分の計算で示し、延長の自然性と合成する。
規約：厳密な自然な逆射は選ばない。使われ方：列の射の厳密化への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra.PointedMapping

/-- 概要：可換な二つの比較のホモトピー逆は写像空間の成分で自然。
方針：片側に比較と逆射の合成を挿入し、可換式を移して反対側で消す。
規約：必要な二つの逆の式だけを成分の等式として指定する。使われ方：選んだ逆射の自然性。 -/
lemma pointedComponentInverse_naturality {A A' B B' : PointedSimplicialSet.{u}}
    (q : A ⟶ B) (q' : A' ⟶ B') (g : B ⟶ A) (g' : B' ⟶ A')
    (e : A ⟶ A') (b : B ⟶ B')
    (hleft : componentOf (q' ≫ g') = componentOf (𝟙 A'))
    (hright : componentOf (g ≫ q) = componentOf (𝟙 B))
    (hn : e ≫ q' = q ≫ b) :
    componentOf (g ≫ e) = componentOf (b ≫ g') := by
  calc
    componentOf (g ≫ e) = componentOf ((g ≫ e) ≫ (q' ≫ g')) := by
      simpa only [Category.comp_id] using componentOf_comp_left hleft.symm (g ≫ e)
    _ = componentOf ((g ≫ q) ≫ (b ≫ g')) := by
      congr 1
      calc
        (g ≫ e) ≫ (q' ≫ g') = g ≫ (e ≫ q') ≫ g' := by simp only [Category.assoc]
        _ = g ≫ (q ≫ b) ≫ g' := by rw [hn]
        _ = (g ≫ q) ≫ (b ≫ g') := by simp only [Category.assoc]
    _ = componentOf (b ≫ g') := by
      simpa only [Category.id_comp] using componentOf_comp_right hright (b ≫ g')

/-- 概要：一次方向の比較の選んだ逆射は写像空間の成分で自然。
方針：両向きの基点固定ホモトピーと元の比較の厳密な自然性を使う。
規約：全ての入力の射に適用。使われ方：境界商の随伴射の自然性。 -/
lemma oneDirectionKanComparisonInverse_naturality_component (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    componentOf (oneDirectionKanComparisonInverse r X ≫
      (oneDirectionKanRealizationFunctor r).map f) =
    componentOf ((boundaryKanRealizationFunctor r).map f ≫
      oneDirectionKanComparisonInverse r Y) := by
  apply pointedComponentInverse_naturality
    ((oneDirectionKanComparisonNat r).app X) ((oneDirectionKanComparisonNat r).app Y)
  · exact ((piZero_eq_iff_pointedHomotopy _ _).mpr
      (oneDirectionKanComparison_inverse_homotopy r Y)).symm
  · exact ((piZero_eq_iff_pointedHomotopy _ _).mpr
      (oneDirectionKanComparisonInverse_homotopy r X)).symm
  · exact (oneDirectionKanComparisonNat r).naturality f

/-- 概要：境界商の随伴射は写像空間の成分で自然。
方針：逆射の自然性と Kan 延長のホモトピー自然性を合成する。
規約：構成に含まれる選択の厳密な自然性は不要。使われ方：反復 S の列の射の構成。 -/
lemma boundaryKanAssemblyAdjoint_naturality_component (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    componentOf ((boundaryKanRealizationFunctor r).map f ≫ boundaryKanAssemblyAdjoint r Y) =
      componentOf (boundaryKanAssemblyAdjoint r X ≫ (loopBoundaryKanFunctor (r + 1)).map f) := by
  let v := (kanAssemblyAdjointChoices_isContractibleKan r X).nonempty.some
  let w := (kanAssemblyAdjointChoices_isContractibleKan r Y).nonempty.some
  have hi := oneDirectionKanComparisonInverse_naturality_component r f
  have hk : componentOf ((oneDirectionKanRealizationFunctor r).map f ≫
      kanAssemblyAdjointAt r Y w) = componentOf (kanAssemblyAdjointAt r X v ≫
        (loopBoundaryKanFunctor (r + 1)).map f) :=
    (piZero_eq_iff_pointedHomotopy _ _).mpr (kanAssemblyAdjointAt_naturality_homotopy r f v w)
  have hi' := componentOf_comp_right hi.symm (kanAssemblyAdjointAt r Y w)
  have hk' := componentOf_comp_left hk (oneDirectionKanComparisonInverse r X)
  change componentOf (_ ≫ (oneDirectionKanComparisonInverse r Y ≫ kanAssemblyAdjointAt r Y w)) =
    componentOf ((oneDirectionKanComparisonInverse r X ≫ kanAssemblyAdjointAt r X v) ≫ _)
  simp only [Category.assoc] at hi' hk' ⊢
  exact hi'.trans hk'

/-- 概要：smash/loop 随伴の uncurry は写像空間の成分の等式を保つ。
方針：uncurry を suspension と余単位への後合成として計算する。
規約：対象の Kan 性は不要。使われ方：随伴射のホモトピー自然性を構造射へ戻す。 -/
lemma pointedComponentUncurry {A B : PointedSimplicialSet.{u}}
    {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B} (h : componentOf f = componentOf g) :
    componentOf ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv A B).symm f) =
      componentOf ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv A B).symm g) := by
  let adj := PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}
  change componentOf ((adj.homEquiv A B).symm f) = componentOf ((adj.homEquiv A B).symm g)
  rw [adj.homEquiv_counit, adj.homEquiv_counit]
  exact componentOf_comp_right (componentOf_suspension h) (adj.counit.app B)

/-- 概要：境界商の suspension 構造射は写像空間の成分で自然。
方針：随伴射の自然性を uncurry し、随伴の両変数の自然性で書き直す。
規約：全ての入力の射に適用。使われ方：列の射のホモトピー可換式。 -/
lemma boundaryKanAssemblySigma_naturality_component (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    componentOf (PointedSimplicialSet.circle.{u} ◁ (boundaryKanRealizationFunctor r).map f ≫
      boundaryKanAssemblySigma r Y) =
      componentOf (boundaryKanAssemblySigma r X ≫
        (boundaryKanRealizationFunctor (r + 1)).map f) := by
  let adj := PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}
  have h := pointedComponentUncurry (boundaryKanAssemblyAdjoint_naturality_component r f)
  change componentOf ((adj.homEquiv _ _).symm
      ((boundaryKanRealizationFunctor r).map f ≫ boundaryKanAssemblyAdjoint r Y)) =
    componentOf ((adj.homEquiv _ _).symm
      (boundaryKanAssemblyAdjoint r X ≫
        (PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}).map
          ((boundaryKanRealizationFunctor (r + 1)).map f))) at h
  rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm] at h
  exact h

/-- 概要：loop の恒等射を uncurry した余単位は標的の射について自然。
方針：smash/loop 随伴の余単位の自然性を明示する。
規約：Kan 性は不要。使われ方：K 空間を零段とする列の構造射の比較。 -/
lemma pointedLoopCounit_naturality {A B : PointedSimplicialSet.{u}} (f : A ⟶ B) :
    PointedSimplicialSet.circle.{u} ◁
      (PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}).map f ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B) B).symm (𝟙 _) =
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace A) A).symm (𝟙 _) ≫ f := by
  let adj := PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}
  change (PointedObject.smashFunctor.obj PointedSimplicialSet.circle.{u}).map
      ((PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}).map f) ≫
        (adj.homEquiv _ _).symm (𝟙 _) = (adj.homEquiv _ _).symm (𝟙 _) ≫ f
  rw [adj.homEquiv_symm_id, adj.homEquiv_symm_id]
  exact adj.counit.naturality f

end SerrePositivity.KST.SConstruction
