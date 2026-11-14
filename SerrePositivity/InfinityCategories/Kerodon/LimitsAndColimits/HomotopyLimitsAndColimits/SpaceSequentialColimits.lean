module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.OppositeSequenceIndex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanCoconeColimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictCoconeLegs
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FilteredKanColimit

/-!
概要：単射な遷移を持つ Kan 複体の可算列の実際の余極限は 𝒮 の逐次余極限となる。
方針：filtered colimit の Kan 性と台の普遍性を使い、全反変 Hom を fibration の塔に移す。
規約：余極限の台は通常の単体集合の colimit のまま保持する。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、F2 の逐次 homotopy 余極限。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

local instance kanSequenceOppositeHomKan (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ) :
    KanComplex (SimplicialCategory.sHom X Y) :=
  inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- 概要：Kan 複体の可算列の台の余極限を Kan 対象に束縛する。
方針：有限ホーンの filtered colimit の一段への因子分解で得た既存の Kan 性を使う。
規約：Kan 性には遷移の単射性を要求しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、𝒮 の実際の逐次余極限対象。 -/
noncomputable def kanSequentialColimitObject (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} := by
  have : ∀ i, KanComplex ((F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).obj i) := fun i ↦
    inferInstanceAs (KanComplex (F.obj i).obj)
  exact ⟨colimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget), inferInstance⟩

/-- 概要：Kan 複体の列の通常の余極限への標準余錐。
方針：台の余極限の包含射と自然性を束縛された対象の射として使う。
規約：頂点は kanSequentialColimitObject F そのもの。
使われ方：HTT 4.2.4.1、𝒮 の逐次余極限の入力余錐。 -/
noncomputable def kanSequentialColimitCocone (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : Cocone F where
  pt := kanSequentialColimitObject F
  ι :=
    { app := fun i ↦ colimit.ι (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) i
      naturality := fun _ _ f ↦ colimit.w (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) f }

/-- 概要：Kan 複体の列の標準余錐の台は単体集合の余極限。
方針：台の包含射を選択された余極限余錐の包含射に同定する。
規約：遷移の単射性を要求しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、全反変 Hom の普遍性の入力。 -/
noncomputable def kanSequentialColimitCocone_forget_isColimit
    (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    IsColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone (kanSequentialColimitCocone F)) :=
  colimit.isColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)

/-- 概要：束縛した逐次余極限余錐は通常の Kan 複体の圏の余極限。
方針：台での普遍性を忘却関手による判定へ渡す。
規約：実際の射の普遍性を主張する。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、逐次余極限の通常の圏での検証。 -/
noncomputable def kanSequentialColimitCocone_isColimit (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    IsColimit (kanSequentialColimitCocone F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectCocone_isColimit_of_forget _ (kanSequentialColimitCocone_forget_isColimit F)

/-- 概要：逐次余極限の全反変豊穣 Hom は標準の塔の添字上で極限を与える。
方針：台の余極限から得た Hom の極限性を添字の圏同値で移す。
規約：X は全ての Kan 対象の反対を動く。
使われ方：HTT 4.2.4.1、fibration の塔の極限定理の Hom 条件。 -/
noncomputable def kanSequentialColimitCocone_homTower_isLimit
    (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone
      ((kanSequentialColimitCocone F).op.whisker _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeSequenceIndex) X) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectOppositeHomCone_isLimit_of_forget _
    (kanSequentialColimitCocone_forget_isColimit F) X).whiskerEquivalence
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeSequenceIndexEquivalence

/-- 概要：単射な遷移の列の反変豊穣 Hom の隣接遷移は Kan fibration。
方針：反対の豊穣 Hom 関手を内部 Hom の前合成へ戻し、単射による前合成の充填性を使う。
規約：全ての X と全ての隣接遷移を扱う。
使われ方：Kerodon 7.5.3.12（Tag 03B1）・7.5.4.6（Tag 03BB）、逐次余極限を Hom の塔で判定する条件。 -/
instance kanSequenceHomTower_map_fibration (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    [∀ n : ℕ, Mono ((F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n))))]
    (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ) (n : ℕ) :
    Fibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeSequenceIndex ⋙ F.op) X).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)) := by
  change Fibration (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ).obj
    (Opposite.op X)).map _)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectOppositeHomFunctor_eq X.unop]
  change Fibration ((pre ((F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map
    (AsSmall.up.map (homOfLE (Nat.le_succ n))))).app X.unop.obj)
  infer_instance

/-- 概要：元の空間値図式上の実際の逐次余極限余錐。
方針：通常の余極限余錐を coherent nerve へ写し、既存の空間値図式に等式で移す。
規約：頂点を Kan 置換せず台の colimit のまま使う。
使われ方：HTT 4.2.4.1、F2 が使う 𝒮 の逐次余極限余錐。 -/
noncomputable def spaceSequentialColimitCocone (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (kanSequentialColimitCocone F))

/-- 概要：逐次余極限余錐の頂点は台の実際の余極限の標準頂点。
方針：図式の等式による移送と通常の余錐の構成は頂点を保持する。
規約：頂点の厳密な等号。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、𝒮 の逐次余極限対象の同定。 -/
lemma spaceSequentialColimitCocone_vertex (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (spaceSequentialColimitCocone F).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (kanSequentialColimitObject F) := by
  rw [spaceSequentialColimitCocone, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent]
  rfl

/-- 概要：逐次余極限余錐の段 n の標準の脚。
方針：元の図式の標準頂点で native な余錐の脚を取る。
規約：段 n は AsSmall の標準持ち上げとして指定する。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、逐次余極限の包含射の同定。 -/
noncomputable def spaceSequentialColimitCoconeLeg (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (n : ℕ) : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentCoconeLegMap (spaceSequentialColimitCocone F)
    (SSet.yonedaEquiv.symm (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (AsSmall.up.obj n))))

/-- 概要：逐次余極限余錐の各脚は台の通常の余極限の包含射の coherent 表示。
方針：図式の移送が脚を保持することと strict な余錐の脚の等式を使う。
規約：脚の同定に遷移の単射性を要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、逐次余極限の具体的な射の照合。 -/
lemma spaceSequentialColimitCoconeLeg_eq (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (n : ℕ) :
    spaceSequentialColimitCoconeLeg F n = SSet.yonedaEquiv.symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ (show F.obj (AsSmall.up.obj n) ⟶ kanSequentialColimitObject F from
          colimit.ι (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (AsSmall.up.obj n)))) := by
  unfold spaceSequentialColimitCoconeLeg spaceSequentialColimitCocone
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentCoconeLegMap_ofDiagramEq]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictNativeCoconeLeg_eq (kanSequentialColimitCocone F) (AsSmall.up.obj n)

/-- 概要：単射な遷移を持つ Kan 複体列の通常の余極限は 𝒮 の逐次余極限を与える。
方針：全反変 Hom の極限性と fibration の塔を使い、再添字と双対化で native な余極限性へ戻す。
規約：全ての隣接遷移の単射性を要求し、Hom の比較同値を追加の仮定にしない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.3.12（Tag 03B1）・7.5.4.6（Tag 03BB）、F2 の逐次 homotopy 余極限。 -/
lemma spaceSequentialColimitCocone_isColimitCone (F : AsSmall.{u} ℕ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    [∀ n : ℕ, Mono ((F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n))))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (spaceSequentialColimitCocone F) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (kanSequentialColimitCocone F))).mp
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_isColimit_iff]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_whisker (kanSequentialColimitCocone F).op
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeSequenceIndex).mpr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_tower_homLimit _
    (kanSequentialColimitCocone_homTower_isLimit F)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
