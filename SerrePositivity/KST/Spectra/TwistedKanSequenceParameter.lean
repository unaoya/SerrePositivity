module

public import SerrePositivity.KST.Spectra.TwistedKanSequenceMaps
public import SerrePositivity.KST.Spectra.MappingKanSequence

/-!
概要：自己射と可換なパラメータ付き列射を、同じパラメータを保つ twist の列射へ移す。
方針：元の構造可換式に、次段の自己射との全パラメータ可換式を合成する。
規約：新しい段射を選ばない。使われ方：符号付き loop 列のパラメータ作用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.KanSequence

/-- 自己射と可換する全パラメータ族を、同じ段射の twist 族へ移す。 -/
def twistParameterHom {A : PointedSimplicialSet.{u}} {X Y : KanSequence.{u}}
    (r : Hom X X) (s : Hom Y Y) (f : Hom X (mapping A Y))
    (h : ∀ n, r.app n ≫ f.app n = f.app n ≫ (ihom A).map (s.app n)) :
    Hom (twist r) (mapping A (twist s)) where
  app := f.app
  comm n := by
    change PointedSimplicialSet.circle.{u} ◁ f.app n ≫
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map PointedSimplicialSet.circle.{u} A (Y.level n).space ≫
          (ihom A).map (Y.sigma n ≫ s.app (n + 1))) =
      (X.sigma n ≫ r.app (n + 1)) ≫ f.app (n + 1)
    calc
      _ = (PointedSimplicialSet.circle.{u} ◁ f.app n ≫ (mapping A Y).sigma n) ≫
          (ihom A).map (s.app (n + 1)) := by
        simp only [mapping, Functor.map_comp, Category.assoc]
      _ = (X.sigma n ≫ f.app (n + 1)) ≫ (ihom A).map (s.app (n + 1)) :=
        congrArg (· ≫ (ihom A).map (s.app (n + 1))) (f.comm n)
      _ = _ := by rw [Category.assoc, ← h (n + 1), ← Category.assoc]

end SerrePositivity.KST.Spectra.KanSequence
