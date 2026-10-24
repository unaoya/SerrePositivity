module
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RightHomUniversal
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.PrecompositionFullFaithfulness
public import SerrePositivity.InfinityCategories.F1B.Localization.Localization
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulCalculus
/-!
概要：各関手が自分の制限の恒等変換による右 Kan 拡張なら、前合成は全写像空間で充満忠実。
方針：右 Kan の Hom 普遍性を全標的で使い、内部 Hom の交換による全パラメータ判定へ渡す。
規約：h Fun のみの結論で止めない。使われ方：商関手の局所化普遍性の充満忠実性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
/-- 標準右 Kan 変換の Hom 普遍性は、指定した前合成写像そのものの全単射性。 -/
lemma rightKanRefl_homMap_bijective {X Q Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] [Quasicategory Y] (q : X ⟶ Q) (F G : Q ⟶ Y)
    (h : IsRightKanExtension q (q ≫ G) G (functorHomotopyRefl (q ≫ G))) :
    Function.Bijective ((hoFunctor.map ((pre q).app Y)).toFunctor.map :
      FunctorHom F G → FunctorHom (q ≫ F) (q ≫ G)) := by
  have hu := F1B.kanRightKanExtension_homUniversal q (functorHomotopyRefl (q ≫ G)) h F
  have he : rightKanHomMap q
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyRefl (q ≫ G)))) F =
      ((hoFunctor.map ((pre q).app Y)).toFunctor.map :
        FunctorHom F G → FunctorHom (q ≫ F) (q ≫ G)) := by
    funext η
    change _ ≫ Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyRefl (q ≫ G))) = _
    rw [functorHomotopyRefl_hom]
    exact Category.comp_id ((hoFunctor.map ((pre q).app Y)).toFunctor.map η)
  exact he ▸ hu
/-- 各関手の標準右 Kan 条件は、指定標的の h Fun における前合成の充満忠実性を与える。 -/
def rightKanPrecompositionHoFullyFaithful {X Q Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] [Quasicategory Y] (q : X ⟶ Q)
    (h : ∀ G : Q ⟶ Y, IsRightKanExtension q (q ≫ G) G (functorHomotopyRefl (q ≫ G))) :
    (hoFunctor.map ((pre q).app Y)).toFunctor.FullyFaithful := by
  have hb (a b : hoFunctor.obj ((ihom Q).obj Y)) : Function.Bijective
      ((hoFunctor.map ((pre q).app Y)).toFunctor.map : (a ⟶ b) → _) := by
    obtain ⟨x, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨y, rfl⟩ := Truncated.HomotopyCategory.mk_surjective b
    obtain ⟨F, rfl⟩ := (functorVertexEquiv Q Y).surjective x
    obtain ⟨G, rfl⟩ := (functorVertexEquiv Q Y).surjective y
    exact rightKanRefl_homMap_bijective q F G (h G)
  have : (hoFunctor.map ((pre q).app Y)).toFunctor.Full := ⟨fun {a b} => (hb a b).2⟩
  have : (hoFunctor.map ((pre q).app Y)).toFunctor.Faithful := ⟨fun {a b} => (hb a b).1⟩
  exact CategoryTheory.Functor.FullyFaithful.ofFullyFaithful _
/-- 全標的での標準右 Kan 条件は、局所化前合成の全写像空間上の充満忠実性を与える。 -/
lemma localizationPrecomposition_isFullyFaithful_of_rightKan {X Q : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] (q : X ⟶ Q) (W : Set (X _⦋1⦌))
    (hq : InvertsEdges q W)
    (h : ∀ (Y : SSet.{u}) [Quasicategory Y], ∀ G : Q ⟶ Y,
      IsRightKanExtension q (q ≫ G) G (functorHomotopyRefl (q ≫ G)))
    (Y : SSet.{u}) [Quasicategory Y] :
    IsFullyFaithful (localizationPrecomposition q W hq Y) := by
  have hp := SerrePositivity.InfinityCategories.F1B.precomposition_isFullyFaithful_of_hoFullyFaithful q
    (fun Z _ => rightKanPrecompositionHoFullyFaithful q (h Z)) Y
  have hi := isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom X).obj Y)
    (IsInvertingFunctorVertex X Y W)
  change IsFullyFaithful (invertingFunctors X Y W).ι at hi
  have hc : IsFullyFaithful (localizationPrecomposition q W hq Y ≫
      (invertingFunctors X Y W).ι) :=
    (congrArg IsFullyFaithful (localizationPrecomposition_ι q W hq Y)).mpr hp
  exact hi.cancel_right hc
end SerrePositivity.InfinityCategories
