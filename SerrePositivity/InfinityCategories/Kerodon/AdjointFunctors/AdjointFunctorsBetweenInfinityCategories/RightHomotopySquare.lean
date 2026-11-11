module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.MappingTranspose
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StdSimplexProductMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero

/-!
概要：右ホモトピーの三角形を両端固定の区間の族へ移す正方形。
方針：頂点 (s,t) を s=0 なら t、s=1 なら 2 に送る単調写像を使う。
規約：第一座標が射の区間、第二座標がホモトピーの時間。
使われ方：Kerodon §4.6.5（Tag 01KW）・Prop 6.2.1.17（Tag 02F1）、h Fun の射の等式から写像空間のホモトピーへ。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：右ホモトピーを正方形にする頂点の単調写像。
方針：射の始点は三角形の 0→1 をたどり、終点は 2 に固定する。
規約：第一座標が射、第二座標が時間。
使われ方：右ホモトピーの両端固定の区間表示。 -/
def rightHomotopySquareOrder : Fin 2 × Fin 2 →o Fin 3 where
  toFun p := if p.1 = 0 then p.2.castSucc else 2
  monotone' := by decide

/-- 概要：右ホモトピーの三角形へ向かう正方形の射。
方針：頂点の単調写像を標準単体の直積の射にする。
規約：対角と後半の辺が時間零と一に現れる。
使われ方：右ホモトピーの写像空間の辺への移送。 -/
def rightHomotopySquare : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[2] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap rightHomotopySquareOrder

/-- 概要：時間零での制限は三角形の対角 0→2。
方針：区間の各頂点で計算する。
規約：時間は第二因子。
使われ方：右ホモトピーの始点の計算。 -/
lemma rightHomotopySquare_zero :
    SSet.ι₀ ≫ rightHomotopySquare.{u} = stdSimplex.δ (1 : Fin 3) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.ext
  intro i
  change (if a i = 0 then (0 : Fin 2).castSucc else 2) =
    (SimplexCategory.δ (1 : Fin 3)).toOrderHom (a i)
  generalize a i = j
  fin_cases j <;> rfl

/-- 概要：時間一での制限は三角形の後半の辺 1→2。
方針：区間の各頂点で計算する。
規約：時間は第二因子。
使われ方：右ホモトピーの終点の計算。 -/
lemma rightHomotopySquare_one :
    SSet.ι₁ ≫ rightHomotopySquare.{u} = stdSimplex.δ (0 : Fin 3) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.ext
  intro i
  change (if a i = 0 then (1 : Fin 2).castSucc else 2) =
    (SimplexCategory.δ (0 : Fin 3)).toOrderHom (a i)
  generalize a i = j
  fin_cases j <;> rfl

/-- 概要：射の始点の辺は三角形の 0→1。
方針：第一因子を零に固定して計算する。
規約：この辺は右ホモトピーの三角形で恒等辺に写る。
使われ方：写像空間の始点を全時間で固定する。 -/
lemma rightHomotopySquare_source :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ rightHomotopySquare = stdSimplex.δ (2 : Fin 3) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.ext
  intro i
  change (if (0 : Fin 2) = 0 then (a i).castSucc else 2) =
    (SimplexCategory.δ (2 : Fin 3)).toOrderHom (a i)
  generalize a i = j
  fin_cases j <;> rfl

/-- 概要：射の終点の辺は三角形の頂点 2 に定値。
方針：第一因子を一に固定して計算する。
規約：全時間で同じ終点。
使われ方：写像空間の終点を固定する。 -/
lemma rightHomotopySquare_target :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ rightHomotopySquare =
      SSet.const (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.ext
  intro i
  rfl

/-- 概要：右ホモトピーの三角形を両端固定の区間の族にする。
方針：三角形を正方形で引き戻し、始点の恒等辺と終点の値を確認する。
規約：時刻零は対角 g、時刻一は後半の辺 f。
使われ方：h Fun の射の等式を写像空間のホモトピーに移す。 -/
noncomputable def rightHomotopyInterval {Z : SSet.{u}} {x y : Z _⦋0⦌}
    {f g : SSet.Truncated.Edge (X := (truncation 2).obj Z) x y}
    (t : SSet.Truncated.Edge.CompStruct
      (SSet.Truncated.Edge.id (X := (truncation 2).obj Z) x) f g) :
    (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyCurry (rightHomotopySquare ≫ SSet.yonedaEquiv.symm t.simplex)
    (by
      rw [← Category.assoc, rightHomotopySquare_source]
      apply SSet.yonedaEquiv.injective
      rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      simp only [SimplicialObject.δ]
      have hd : SSet.yonedaEquiv (SSet.const x : (Δ[1] : SSet.{u}) ⟶ Z) =
          (SSet.Truncated.Edge.id (X := (truncation 2).obj Z) x).edge :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one x
      rw [hd]
      exact t.d₂)
    (by
      rw [← Category.assoc, rightHomotopySquare_target, SSet.const_comp]
      congr 1
      change Z.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ 2).op t.simplex = y
      have hc : SimplexCategory.const ⦋0⦌ ⦋2⦌ 2 =
          SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3) := by decide
      rw [hc, op_comp, CategoryTheory.Functor.map_comp_apply]
      have ht : Z.map (SimplexCategory.δ (0 : Fin 3)).op t.simplex = f.edge := t.d₀
      rw [ht]
      exact f.tgt_eq)

/-- 概要：右ホモトピーの区間族を展開すると三角形の正方形での引き戻し。
方針：区間模型の端点指定の普遍性を使う。
規約：t は指定された三角形そのもの。
使われ方：ホモトピーの端点計算。 -/
lemma rightHomotopyInterval_uncurry {Z : SSet.{u}} {x y : Z _⦋0⦌}
    {f g : SSet.Truncated.Edge (X := (truncation 2).obj Z) x y}
    (t : SSet.Truncated.Edge.CompStruct
      (SSet.Truncated.Edge.id (X := (truncation 2).obj Z) x) f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (rightHomotopyInterval t) =
      rightHomotopySquare ≫ SSet.yonedaEquiv.symm t.simplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyUncurry_curry _ _ _

/-- 概要：右ホモトピーの転置した区間族の時間零での値。
方針：転置の区間交換と三角形の面の式を使う。
規約：パラメータ A を持つ定値関手間の辺を扱う。
使われ方：写像空間の族のホモトピーの端点。 -/
lemma rightHomotopyIntervalFamily_zero {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y))}
    (t : SSet.Truncated.Edge.CompStruct
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x))) f g) :
    SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyTranspose (rightHomotopyInterval t) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyOfEdge g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective x y
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyTranspose_uncurry]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyOfEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyUncurry_curry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalTransposeUncurry
  rw [rightHomotopyInterval_uncurry, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalParameterSwap_time_zero,
    Category.assoc, ← uncurry_natural_left, ← Category.assoc, rightHomotopySquare_zero]
  have h : stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm t.simplex =
      (SSet.yonedaEquiv (X := (ihom A).obj X) (n := ⦋1⦌)).symm g.edge := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
    simp only [SimplicialObject.δ, Equiv.apply_symm_apply]
    have ht := t.d₁
    change ((ihom A).obj X).map (SimplexCategory.δ (1 : Fin 3)).op t.simplex = g.edge at ht
    exact ht
  rw [h]

/-- 概要：右ホモトピーの転置した区間族の時間一での値。
方針：転置の区間交換と三角形の面の式を使う。
規約：パラメータ A を持つ定値関手間の辺を扱う。
使われ方：写像空間の族のホモトピーの端点。 -/
lemma rightHomotopyIntervalFamily_one {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y))}
    (t : SSet.Truncated.Edge.CompStruct
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x))) f g) :
    SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyTranspose (rightHomotopyInterval t) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyOfEdge f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective x y
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyTranspose_uncurry]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyOfEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyUncurry_curry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalTransposeUncurry
  rw [rightHomotopyInterval_uncurry, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalParameterSwap_time_one,
    Category.assoc, ← uncurry_natural_left, ← Category.assoc, rightHomotopySquare_one]
  have h : stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm t.simplex =
      (SSet.yonedaEquiv (X := (ihom A).obj X) (n := ⦋1⦌)).symm f.edge := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
    simp only [SimplicialObject.δ, Equiv.apply_symm_apply]
    have ht := t.d₀
    change ((ihom A).obj X).map (SimplexCategory.δ (0 : Fin 3)).op t.simplex = f.edge at ht
    exact ht
  rw [h]

/-- 概要：定値関手間の右ホモトピーは区間模型の族のホモトピーを与える。
方針：三角形を正方形へ引き戻して転置し、時間零・一の値を計算する。
規約：quasicategory 性は不要。指定された三角形を用いる。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1）、h Fun の射の等式から族のホモトピーへの橋。 -/
noncomputable def intervalFamilyHomotopyOfRightHomotopy {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y))}
    (t : SSet.Truncated.Edge.CompStruct
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x))) f g) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyOfEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyOfEdge f) where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyTranspose (rightHomotopyInterval t)
  h₀ := rightHomotopyIntervalFamily_zero t
  h₁ := rightHomotopyIntervalFamily_one t
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：区間模型の族が h Fun で同じ射を表せば二つの族はホモトピック。
方針：h Fun の射の等式を辺の左ホモトピーへ戻し、右ホモトピーへ変換して転置する。
規約：標的 X は quasicategory、パラメータ A は任意。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1）、パラメータ付き Hom の表示の単射性。 -/
lemma intervalFamilyHom_eq_imp_homotopy {A X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom f = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom g) : Nonempty (SSet.Homotopy f g) := by
  change SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge f) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge g) at h
  have h₂ : SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge g) =
      SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge f) := by
    have hh := congrArg
      (fun m ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((truncation 2).obj ((ihom A).obj X))).map m) h.symm
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory,
      SSet.Truncated.HomotopyCategory.lift_map_homMk] using hh
  have hh : SSet.Truncated.HomotopicL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge f) :=
    Quotient.exact h₂
  obtain ⟨t⟩ := SSet.Truncated.HomotopicL.homotopicR hh
  exact ⟨by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyOfEdge_edge] using
    intervalFamilyHomotopyOfRightHomotopy t⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
