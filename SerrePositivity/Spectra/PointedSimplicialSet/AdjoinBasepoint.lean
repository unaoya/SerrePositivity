module

public import SerrePositivity.Spectra.PointedSimplicialSet.Monoidal

/-! # 通常の単体的集合への自由な基点の追加 -/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.MonoidalCategory

/-- 通常の単体的集合に別の成分として自由な基点を追加する。 -/
def adjoinBasepoint (K : SSet.{u}) : PointedSimplicialSet.{u} := PointedObject.adjoin K

/-- 自由な基点の追加の関手。 -/
def adjoinBasepointFunctor : SSet.{u} ⥤ PointedSimplicialSet.{u} :=
  PointedObject.adjoinFunctor

/-- 自由な基点の追加と忘却の随伴。 -/
def adjoinBasepointAdjunction : adjoinBasepointFunctor.{u} ⊣ forget.{u} :=
  PointedObject.adjoinForgetAdjunction

/-- 終単体的集合への基点の追加はsmashの単位となる。 -/
def adjoinBasepointUnitIso : adjoinBasepoint (𝟙_ SSet.{u}) ≅ 𝟙_ PointedSimplicialSet.{u} :=
  Iso.refl _

end SerrePositivity.PointedSimplicialSet
