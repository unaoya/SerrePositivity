module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.OverPostMapCompatibility
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan

/-!
概要：添字関手は Bousfield–Kan 重みの自然な比較を誘導する。
方針：各 Over 圏への後合成関手の nerve を取る。
規約：重みはここでは共変に述べ、coend には反対関手へ適用する。
使われ方：coend の添字変更の標準比較と Over の図式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {I J K : Type u} [SmallCategory I] [SmallCategory J] [SmallCategory K]

/-- 概要：添字関手により各 Over 圏の nerve を像の Over 圏へ送る。
方針：Over.post の後合成との厳密な可換性を nerve に移す。
規約：U の cofinality は不要。使われ方：Bousfield–Kan coend の添字変更。 -/
def bousfieldKanWeightPost (U : J ⥤ I) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight J ⟶ U ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I where
  app j := nerveMap (Over.post U (X := j))
  naturality i j f := by
    change nerveMap (Over.map f) ≫ nerveMap (Over.post U) =
      nerveMap (Over.post U) ≫ nerveMap (Over.map (U.map f))
    calc
      _ = nerveMap (Over.map f ⋙ Over.post U) :=
        (nerveFunctor.map_comp (Over.map f).toCatHom (Over.post U).toCatHom).symm
      _ = nerveMap (Over.post U ⋙ Over.map (U.map f)) :=
        congrArg (fun V ↦ nerveMap V) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overPost_map_eq U f)
      _ = _ := nerveFunctor.map_comp (Over.post U).toCatHom (Over.map (U.map f)).toCatHom

/-- 概要：恒等の添字関手の重み比較は恒等変換。
方針：各 Over への恒等の後合成の nerve を計算する。
規約：元の重みを保持する。使われ方：coend の添字変更の単位則。 -/
lemma bousfieldKanWeightPost_id (I : Type u) [SmallCategory I] :
    bousfieldKanWeightPost (𝟭 I) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) := by
  apply NatTrans.ext
  funext i
  change nerveMap (Over.post (𝟭 I) (X := i)) = 𝟙 _
  exact nerveFunctor.map_id (Cat.of (Over i))

/-- 概要：合成関手の重み比較は二段の重み比較の合成。
方針：Over.post の合成則と nerve の合成保存を各成分で使う。
規約：先に V、次に U を適用する。使われ方：coend の添字変更の関手性。 -/
lemma bousfieldKanWeightPost_comp (U : J ⥤ I) (V : K ⥤ J) :
    bousfieldKanWeightPost (V ⋙ U) =
      bousfieldKanWeightPost V ≫ Functor.whiskerLeft V (bousfieldKanWeightPost U) := by
  apply NatTrans.ext
  funext i
  change nerveMap (Over.post (V ⋙ U) (X := i)) =
    nerveMap (Over.post V (X := i)) ≫ nerveMap (Over.post U (X := V.obj i))
  exact nerveFunctor.map_comp (Over.post V (X := i)).toCatHom (Over.post U).toCatHom

end SerrePositivity.InfinityCategories.Project.FilteredExchange
