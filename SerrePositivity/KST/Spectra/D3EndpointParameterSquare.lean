module

public import SerrePositivity.KST.Spectra.D3PointedKanParameterSquare
public import SerrePositivity.KST.Spectra.PointedEndpointLoopPullback

/-!
概要：元の区間端点とその cofiber の実四角パラメータ図式を全 Kan 入力で評価する。
方針：元の包含・cofiber 商射・一点への射を同じ順序図式の恒等・合成で固定する。
規約：一般パラメータ図式を未供給入力に残さず、実際の端点円図式へ代入する。
使われ方：d3 の通常点つき loop と実段 loop 図式始点との全関手比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3EndpointSquareOrderCategory : SmallCategory (Fin 2 × Fin 2) :=
  Preorder.smallCategory (Fin 2 × Fin 2)

/-- 元の端点 cofiber 四角形の四パラメータ。 -/
def d3EndpointParameterObj (p : Fin 2 × Fin 2) : PointedSimplicialSet.{u} :=
  if p.1 = 0 then
    if p.2 = 0 then endpointCircle else PointedObject.point
  else if p.2 = 0 then _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval else 𝟙_ PointedSimplicialSet.{u}

/-- 四角の逆向きの各辺は、元の端点包含・cofiber 商・一点の射そのもの。 -/
def d3EndpointParameterMap (s t : Fin 2 × Fin 2) (h : t ≤ s) :
    d3EndpointParameterObj.{u} s ⟶ d3EndpointParameterObj t := by
  rcases s with ⟨i, j⟩
  rcases t with ⟨k, l⟩
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    by_cases hk : k = 0 <;> by_cases hl : l = 0
  all_goals first
    | subst i
    | (have he : i = 1 := by omega
       subst i)
  all_goals first
    | subst j
    | (have he : j = 1 := by omega
       subst j)
  all_goals first
    | subst k
    | (have he : k = 1 := by omega
       subst k)
  all_goals first
    | subst l
    | (have he : l = 1 := by omega
       subst l)
  all_goals try (have h₁ := h.1; norm_num [Fin.le_def] at h₁)
  all_goals try (have h₂ := h.2; norm_num [Fin.le_def] at h₂)
  · exact 𝟙 _
  · exact PointedObject.fromPoint endpointCircle
  · exact 𝟙 _
  · exact pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint
  · exact 𝟙 _
  · exact 0
  · exact PointedObject.toPoint (𝟙_ PointedSimplicialSet.{u})
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint
  · exact 𝟙 _

lemma d3EndpointParameterMap_id (s : Fin 2 × Fin 2) :
    d3EndpointParameterMap.{u} s s le_rfl = 𝟙 _ := by
  rcases s with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> rfl

lemma d3EndpointParameterMap_comp (s t r : Fin 2 × Fin 2) (h : t ≤ s) (h' : r ≤ t) :
    d3EndpointParameterMap.{u} s r (le_trans h' h) =
      d3EndpointParameterMap s t h ≫ d3EndpointParameterMap t r h' := by
  rcases s with ⟨i, j⟩
  rcases t with ⟨k, l⟩
  rcases r with ⟨a, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> fin_cases a <;> fin_cases b
  all_goals try (have h₁ := h.1; norm_num [Fin.le_def] at h₁)
  all_goals try (have h₂ := h.2; norm_num [Fin.le_def] at h₂)
  all_goals try (have h₃ := h'.1; norm_num [Fin.le_def] at h₃)
  all_goals try (have h₄ := h'.2; norm_num [Fin.le_def] at h₄)
  all_goals simp [d3EndpointParameterMap, d3EndpointParameterObj,
    pointedCofiberProjection_zero, PointedObject.toPoint_comp_fromPoint]

/-- 元の実 cofiber 四角形を厳密な四角パラメータ関手として束ねる。 -/
def d3EndpointParameter : (Fin 2 × Fin 2)ᵒᵖ ⥤ PointedSimplicialSet.{u} where
  obj s := d3EndpointParameterObj s.unop
  map {s t} f := d3EndpointParameterMap s.unop t.unop (leOfHom f.unop)
  map_id s := d3EndpointParameterMap_id s.unop
  map_comp {s t r} f g :=
    d3EndpointParameterMap_comp s.unop t.unop r.unop (leOfHom f.unop) (leOfHom g.unop)

/-- 実際の同じ端点円・path・一点・単位パラメータを全 Kan 入力で同時評価。 -/
def d3EndpointParameterSquare : PointedKanInfinity.{u} ⟶
    (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity :=
  d3PointedKanParameterSquare d3EndpointParameter

/-- 元の全端点円作用は、構成済み実パラメータ四角形族の始点である。 -/
lemma d3EndpointParameterSquare_source :
    d3EndpointParameterSquare.{u} ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2),
        stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom endpointCircle) :=
  d3PointedKanParameterSquare_corner d3EndpointParameter 0 0

/-- 右零角は元の区間からの Hom の全作用そのもの。 -/
lemma d3EndpointParameterSquare_path :
    d3EndpointParameterSquare.{u} ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
        stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval) :=
  d3PointedKanParameterSquare_corner d3EndpointParameter 1 0

/-- 他の零角は元の一点からの Hom の全作用そのもの。 -/
lemma d3EndpointParameterSquare_point :
    d3EndpointParameterSquare.{u} ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2),
        stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom PointedObject.point) :=
  d3PointedKanParameterSquare_corner d3EndpointParameter 0 1

/-- 終点は元の単位パラメータからの Hom の全作用。単位同型との接続は別途行う。 -/
lemma d3EndpointParameterSquare_target :
    d3EndpointParameterSquare.{u} ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
        stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})) :=
  d3PointedKanParameterSquare_corner d3EndpointParameter 1 1

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
