module
public import SerrePositivity.InfinityCategories.Derived.MooreUniverse
public import SerrePositivity.InfinityCategories.Derived.MooreCyclesNaturality
/-!
概要：Moore 正規化と宇宙持ち上げの比較が、元の実加群射と可換することを示す。
方針：全次数で元の単体への包含を合成して検査する。
規約：係数・加群・追加宇宙を独立に保ち、既存の比較同型をそのまま使う。
使われ方：評価ホモロジーの自然性を実 pinched 模型の正規化へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory AlgebraicTopology
variable {R : Type u} [CommRing R]
  {W V : SimplicialObject (ModuleCat.{v} R)}

lemma dgBarCompactMooreUliftIso_naturality (f : W ⟶ V) :
    (normalizedMooreComplex (ModuleCat.{max v w} R)).map
        (Functor.whiskerRight f (ModuleCat.uliftFunctor.{w} R)) ≫
      (mooreUliftIso.{u, v, w} V).hom =
    (mooreUliftIso.{u, v, w} W).hom ≫
      ((ModuleCat.uliftFunctor.{w} R).mapHomologicalComplex (.down ℕ)).map
        ((normalizedMooreComplex (ModuleCat.{v} R)).map f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_mono ((ModuleCat.uliftFunctor.{w} R).map
    (NormalizedMooreComplex.objX V n).arrow)).mp
  change (((normalizedMooreComplex (ModuleCat.{max v w} R)).map
    (Functor.whiskerRight f (ModuleCat.uliftFunctor.{w} R))).f n ≫
      (mooreUliftTermIso V n).hom) ≫ _ =
    ((mooreUliftTermIso W n).hom ≫
      (ModuleCat.uliftFunctor.{w} R).map
        (((normalizedMooreComplex (ModuleCat.{v} R)).map f).f n)) ≫ _
  simp only [Category.assoc]
  rw [mooreUliftTermIso_arrow,
    normalizedMooreMap_arrow]
  rw [← Functor.map_comp, normalizedMooreMap_arrow, Functor.map_comp,
    ← Category.assoc, mooreUliftTermIso_arrow]
  rfl

end SerrePositivity.InfinityCategories
