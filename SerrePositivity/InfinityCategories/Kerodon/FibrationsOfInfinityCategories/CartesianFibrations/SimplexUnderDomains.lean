module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ScaffoldFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-!
概要：単体圏の undercategory の nerve を、その始点の標準単体へ自然に写す。
方針：各構造射で戻した初頂点を座標に取り、under の可換三角形を使う。
規約：全次数と全ての単体作用素について自然。
使われ方：共同切断図式と初頂点写像の引き戻しの strict transport の比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：under の各構造射の初頂点を始点の単体内へ戻す単調な座標。
方針：構造射の三角形の可換性と単調性を使う。
規約：under の射列の長さは任意。
使われ方：標準単体への単体的な射の次数ごとの座標。 -/
def transportSimplexUnderOrderHom {B : SSet.{u}} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)
    {n : ℕ} (τ : ComposableArrows (Under s) n) :
    Fin (n + 1) →o Fin (s.objDown.obj.unop.len + 1) where
  toFun i := (τ.obj i).hom.down.hom.unop.toOrderHom 0
  monotone' i j hij := by
    have h := (τ.map (homOfLE hij)).w
    change (τ.obj i).hom ≫ (τ.map (homOfLE hij)).right = (τ.obj j).hom at h
    change (τ.obj i).hom.down.hom.unop.toOrderHom 0 ≤
      (τ.obj j).hom.down.hom.unop.toOrderHom 0
    rw [← h]
    exact (τ.obj i).hom.down.hom.unop.toOrderHom.monotone (Fin.zero_le _)

/-- 概要：under の初頂点座標を単体圏の射として表示する。
方針：単調写像を標準単体の作用素へ変換する。
規約：終域は under の始点の単体。
使われ方：底との可換性の計算。 -/
def transportSimplexUnderMorphism {B : SSet.{u}} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)
    {n : ℕ} (τ : ComposableArrows (Under s) n) :
    ⦋n⦌ ⟶ s.objDown.obj.unop :=
  SimplexCategory.mkHom (transportSimplexUnderOrderHom s τ)

/-- 概要：under の nerve から始点の標準単体への自然な射。
方針：全次数の構造射の初頂点座標を束ねる。
規約：面と退化に対する自然性を同じ式で証明する。
使われ方：単体上の切断を under の切断へ制限する。 -/
def transportSimplexUnderDomainMap {B : SSet.{u}} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) :
    nerve (Under s) ⟶ stdSimplex.obj s.objDown.obj.unop where
  app _ := ↾fun τ ↦ stdSimplex.objEquiv.symm (transportSimplexUnderMorphism s τ)
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro τ
    apply stdSimplex.ext
    intro i
    rfl

/-- 概要：under の構造射の初頂点座標は忘却した射列の初頂点座標を覆う。
方針：各構造射を零番目の構造射と射列内の射へ分解する。
規約：単体圏の射の厳密な等式。
使われ方：元の底への二つの評価の一致。 -/
lemma transportSimplexUnderMorphism_factor {B : SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) {n : ℕ} (τ : ComposableArrows (Under s) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism (τ ⋙ Under.forget s) ≫
      (τ.obj 0).hom.down.hom.unop = transportSimplexUnderMorphism s τ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  have h := (τ.map (homOfLE (Fin.zero_le i))).w
  exact congrArg (fun f : s ⟶ (τ.obj i).right ↦
    f.down.hom.unop.toOrderHom 0) h

/-- 概要：under の標準単体への射は元の底の初頂点写像を覆う。
方針：構造射の単体の条件と初頂点座標の因子分解を使う。
規約：元の底は任意の単体集合。
使われ方：切断制限を底上の相対関手空間の射にする。 -/
lemma transportSimplexUnderDomainMap_projection {B : SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) :
    transportSimplexUnderDomainMap s ≫ SSet.yonedaEquiv.symm s.objDown.val =
      nerveMap (Under.forget s) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro τ
  change B.map (transportSimplexUnderMorphism s τ).op s.objDown.val =
    B.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism (τ ⋙ Under.forget s)).op
      (τ.obj 0).right.objDown.val
  rw [← (τ.obj 0).hom.down.map_val]
  change _ = (B.map (τ.obj 0).hom.down.hom ≫
    B.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism (τ ⋙ Under.forget s)).op) s.objDown.val
  rw [← B.map_comp]
  exact congrArg (fun α ↦ B.map α.op s.objDown.val)
    (transportSimplexUnderMorphism_factor s τ).symm

/-- 概要：under の標準単体への射は単体圏の射に関して自然。
方針：構造射の前合成と標準単体の作用を各座標で計算する。
規約：面と退化の両方を含む。
使われ方：共同切断の制限全体を一つの図式の比較へ束ねる。 -/
lemma transportSimplexUnderDomainMap_naturality {B : SSet.{u}}
    {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B} (f : s ⟶ t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f ≫ transportSimplexUnderDomainMap s =
      transportSimplexUnderDomainMap t ≫ stdSimplex.map f.down.hom.unop := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro τ
  apply stdSimplex.ext
  intro i
  rfl

/-- 概要：under の恒等射の頂点は始点の単体の初頂点へ写る。
方針：恒等射の初頂点座標を計算する。
規約：頂点の厳密な等式。
使われ方：切断制限の成分の同値性を初頂点評価で検出する。 -/
lemma transportSimplexUnderDomainMap_initial {B : SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) :
    (transportSimplexUnderDomainMap s).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 s))) =
      stdSimplex.obj₀Equiv.symm (0 : Fin (s.objDown.obj.unop.len + 1)) := by
  apply stdSimplex.ext
  intro i
  fin_cases i
  rfl

/-- 概要：under の始対象の点包含は標準単体の初頂点包含へ写る。
方針：点の Yoneda 表示の後合成と初頂点の公式を使う。
規約：点からの射の厳密な等式。
使われ方：切断制限の成分を共通の始点の評価で比較する。 -/
lemma transportSimplexUnderDomainMap_initialPoint {B : SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (Under.mk (𝟙 s)) ≫ transportSimplexUnderDomainMap s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex s.objDown.obj.unop.len := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint, SSet.yonedaEquiv_symm_comp, transportSimplexUnderDomainMap_initial]
  rfl

/-- 概要：単体圏の各対象の under の nerve を元の底上の反変図式へ束ねる。
方針：under の忘却を初頂点写像へ合成し、射を under の前合成とする。
規約：底は通常の圏の nerve に限定しない。
使われ方：初頂点写像の引き戻しの strict transport の定義域。 -/
def transportSimplexUnderDomains (B : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)ᵒᵖ ⥤ Over B where
  obj s := Over.mk (nerveMap (Under.forget s.unop) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B)
  map {s t} f := Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f.unop) (by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f.unop ≫
      (nerveMap (Under.forget t.unop) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B) =
      nerveMap (Under.forget s.unop) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_projection])
  map_id s := by
    apply Over.OverMorphism.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_id s.unop
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap_comp g.unop f.unop

/-- 概要：under の定義域の反変図式は単体の定義域の図式へ自然に写る。
方針：標準単体への射の底との可換性と単体圏の射に関する自然性を使う。
規約：普通の自然変換として全ての面・退化を同時に保つ。
使われ方：切断図式と strict transport の全高次の比較の入力。 -/
def transportSimplexUnderDomainTransformation (B : SSet.{u}) :
    transportSimplexUnderDomains B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B where
  app s := Over.homMk (transportSimplexUnderDomainMap s.unop)
    (transportSimplexUnderDomainMap_projection s.unop)
  naturality s t f := by
    apply Over.OverMorphism.ext
    exact transportSimplexUnderDomainMap_naturality f.unop

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
