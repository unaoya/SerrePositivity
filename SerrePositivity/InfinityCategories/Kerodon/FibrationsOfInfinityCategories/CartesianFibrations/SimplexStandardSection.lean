module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexFirstVertexNaturality

/-!
概要：標準単体の単体圏の初頂点関手と、その切断。
方針：有限順序上の上端で切り詰める平行移動を使う。
規約：切断の全対象は同じ次数に取り、恒等射と合成を厳密に保つ。
使われ方：始点を保つ射に関する局所化の標準単体上の比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 標準単体の各単体から、その初頂点を取り出す通常の関手。 -/
def transportStandardFirstVertex (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (Δ[n] : SSet.{u}) ⥤ ULift.{u} (Fin (n + 1)) where
  obj s := ULift.up (s.objDown.val.down.toOrderHom 0)
  map {s t} f := homOfLE (by
    have h := congrArg (fun x ↦ x.down.toOrderHom 0) f.down.map_val
    change s.objDown.val.down.toOrderHom
      (f.down.hom.unop.toOrderHom 0) = t.objDown.val.down.toOrderHom 0 at h
    change s.objDown.val.down.toOrderHom 0 ≤ t.objDown.val.down.toOrderHom 0
    rw [← h]
    exact s.objDown.val.down.toOrderHom.monotone (Fin.zero_le _))

/-- 上端で切り詰めた有限順序の平行移動。 -/
def transportStandardShift (n k : ℕ) : Fin (n + 1) →o Fin (n + 1) where
  toFun i := ⟨min (k + i.val) n, by omega⟩
  monotone' := fun _ _ h ↦ min_le_min_right n (Nat.add_le_add_left h k)

/-- 零による平行移動は恒等写像。 -/
lemma transportStandardShift_zero (n : ℕ) : transportStandardShift n 0 = OrderHom.id := by
  apply OrderHom.ext
  funext i
  apply Fin.ext
  change min (0 + i.val) n = i.val
  have hi := i.isLt
  omega

/-- 上端で切り詰める平行移動の合成則。 -/
lemma transportStandardShift_comp (n k l : ℕ) :
    (transportStandardShift n k).comp (transportStandardShift n l) =
      transportStandardShift n (k + l) := by
  apply OrderHom.ext
  funext i
  apply Fin.ext
  change min (k + min (l + i.val) n) n = min (k + l + i.val) n
  omega

/-- 初頂点 i を持つ、次数 n の標準的な単体。 -/
def transportStandardSectionObj {n : ℕ} (i : ULift.{u} (Fin (n + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (Δ[n] : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (stdSimplex.objEquiv.symm
    (SimplexCategory.mkHom (transportStandardShift n i.down.val)))

/-- 順序射を、平行移動による単体の制限へ写す。 -/
def transportStandardSectionMap {n : ℕ} {i j : ULift.{u} (Fin (n + 1))} (f : i ⟶ j) :
    transportStandardSectionObj i ⟶ transportStandardSectionObj j :=
  ⟨{ hom := (SimplexCategory.mkHom
      (transportStandardShift n (j.down.val - i.down.val))).op
     map_val := by
       apply ULift.ext
       apply SimplexCategory.Hom.ext
       apply OrderHom.ext
       funext k
       apply Fin.ext
       have hij := leOfHom f
       change i.down.val ≤ j.down.val at hij
       change min (i.down.val + min (j.down.val - i.down.val + k.val) n) n =
         min (j.down.val + k.val) n
       omega }⟩

/-- 初頂点関手の標準的な切断。 -/
def transportStandardSection (n : ℕ) :
    ULift.{u} (Fin (n + 1)) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (Δ[n] : SSet.{u}) where
  obj := transportStandardSectionObj
  map := transportStandardSectionMap
  map_id i := by
    apply ULift.ext
    apply CategoryTheory.Functor.Elements.Hom.ext
    change (SimplexCategory.mkHom (transportStandardShift n
      (i.down.val - i.down.val))).op = (𝟙 _).op
    congr 1
    apply SimplexCategory.Hom.ext
    rw [Nat.sub_self, transportStandardShift_zero]
    rfl
  map_comp {i j k} f g := by
    apply ULift.ext
    apply CategoryTheory.Functor.Elements.Hom.ext
    change (SimplexCategory.mkHom (transportStandardShift n
      (k.down.val - i.down.val))).op =
      ((SimplexCategory.mkHom (transportStandardShift n
        (k.down.val - j.down.val))) ≫
        SimplexCategory.mkHom (transportStandardShift n
          (j.down.val - i.down.val))).op
    congr 1
    apply SimplexCategory.Hom.ext
    change transportStandardShift n (k.down.val - i.down.val) =
      (transportStandardShift n (j.down.val - i.down.val)).comp
        (transportStandardShift n (k.down.val - j.down.val))
    rw [transportStandardShift_comp]
    have hij := leOfHom f
    have hjk := leOfHom g
    change i.down.val ≤ j.down.val at hij
    change j.down.val ≤ k.down.val at hjk
    congr 1
    omega

/-- 切断の初頂点は、元の有限順序の頂点に等しい。 -/
lemma transportStandardSection_firstVertex (n : ℕ) :
    transportStandardSection.{u} n ⋙ transportStandardFirstVertex n = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  apply ULift.ext
  apply Fin.ext
  change min (i.down.val + 0) n = i.down.val
  have hi := i.down.isLt
  omega

/-- 単体の各頂点から初頂点を引いて得られる単調写像。 -/
def transportStandardSectionComparisonOrder {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (Δ[n] : SSet.{u})) :
    Fin (s.objDown.obj.unop.len + 1) →o Fin (n + 1) where
  toFun k := ⟨(s.objDown.val.down.toOrderHom k).val -
    (s.objDown.val.down.toOrderHom 0).val, by
      have hk := (s.objDown.val.down.toOrderHom k).isLt
      change (s.objDown.val.down.toOrderHom k).val < n + 1 at hk
      omega⟩
  monotone' := fun _ _ h ↦ Nat.sub_le_sub_right
    (s.objDown.val.down.toOrderHom.monotone h) _

/-- 初頂点による標準単体から、指定された単体への比較射。 -/
def transportStandardSectionComparisonApp {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (Δ[n] : SSet.{u})) :
    (transportStandardSection n).obj ((transportStandardFirstVertex n).obj s) ⟶ s :=
  ⟨{ hom := (SimplexCategory.mkHom (transportStandardSectionComparisonOrder s)).op
     map_val := by
       apply ULift.ext
       apply SimplexCategory.Hom.ext
       apply OrderHom.ext
       funext k
       apply Fin.ext
       have hk := (s.objDown.val.down.toOrderHom k).isLt
       change (s.objDown.val.down.toOrderHom k).val < n + 1 at hk
       have h0 := s.objDown.val.down.toOrderHom.monotone (Fin.zero_le k)
       change (s.objDown.val.down.toOrderHom 0).val ≤
         (s.objDown.val.down.toOrderHom k).val at h0
       change min ((s.objDown.val.down.toOrderHom 0).val +
         ((s.objDown.val.down.toOrderHom k).val -
           (s.objDown.val.down.toOrderHom 0).val)) n =
         (s.objDown.val.down.toOrderHom k).val
       omega }⟩

/-- 標準切断から恒等関手への、全単体に自然な比較。 -/
def transportStandardSectionComparison (n : ℕ) :
    transportStandardFirstVertex n ⋙ transportStandardSection.{u} n ⟶ 𝟭 _ where
  app := transportStandardSectionComparisonApp
  naturality {s t} f := by
    apply ULift.ext
    apply CategoryTheory.Functor.Elements.Hom.ext
    change ((SimplexCategory.mkHom (transportStandardSectionComparisonOrder t)) ≫
      SimplexCategory.mkHom (transportStandardShift n
        ((t.objDown.val.down.toOrderHom 0).val -
          (s.objDown.val.down.toOrderHom 0).val))).op =
      (f.down.hom.unop ≫
        SimplexCategory.mkHom (transportStandardSectionComparisonOrder s)).op
    congr 1
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    apply Fin.ext
    have hv := congrArg (fun x ↦ (x.down.toOrderHom k).val) f.down.map_val
    change (s.objDown.val.down.toOrderHom (f.down.hom.unop.toOrderHom k)).val =
      (t.objDown.val.down.toOrderHom k).val at hv
    have hij := leOfHom ((transportStandardFirstVertex n).map f)
    change (s.objDown.val.down.toOrderHom 0).val ≤
      (t.objDown.val.down.toOrderHom 0).val at hij
    have h0 := t.objDown.val.down.toOrderHom.monotone (Fin.zero_le k)
    change (t.objDown.val.down.toOrderHom 0).val ≤
      (t.objDown.val.down.toOrderHom k).val at h0
    have hk := (t.objDown.val.down.toOrderHom k).isLt
    change (t.objDown.val.down.toOrderHom k).val < n + 1 at hk
    change min (((t.objDown.val.down.toOrderHom 0).val -
      (s.objDown.val.down.toOrderHom 0).val) +
      ((t.objDown.val.down.toOrderHom k).val -
        (t.objDown.val.down.toOrderHom 0).val)) n =
      (s.objDown.val.down.toOrderHom (f.down.hom.unop.toOrderHom k)).val -
        (s.objDown.val.down.toOrderHom 0).val
    omega

/-- 比較の各成分は、単体圏で始点を保つ射。 -/
lemma transportStandardSectionComparison_preservesFirst {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (Δ[n] : SSet.{u})) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexPreservesFirst ((transportStandardSectionComparison n).app s) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexPreservesFirst_iff _).mpr
  apply Fin.ext
  change (s.objDown.val.down.toOrderHom 0).val -
    (s.objDown.val.down.toOrderHom 0).val = 0
  exact Nat.sub_self _

/-- 標準単体上の通常の初頂点関手は、既存の初頂点写像を全次数で回収する。 -/
lemma transportStandardFirstVertex_nerve (n : ℕ) :
    nerveMap (transportStandardFirstVertex.{u} n) ≫ (stdSimplex.isoNerve n).inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap (Δ[n] : SSet.{u}) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro σ
  apply ULift.ext
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  have hv := congrArg (fun x ↦ x.down.toOrderHom 0)
    (σ.map (homOfLE (Fin.zero_le i))).down.map_val
  exact hv.symm

/-- 標準単体上の初頂点写像の実際の単体的な切断。 -/
def transportStandardFirstVertexSection (n : ℕ) :
    (Δ[n] : SSet.{u}) ⟶ nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (Δ[n] : SSet.{u})) :=
  (stdSimplex.isoNerve n).hom ≫ nerveMap (transportStandardSection n)

/-- 初頂点写像は標準単体上で厳密な右逆を持つ。 -/
lemma transportStandardFirstVertexSection_comp (n : ℕ) :
    transportStandardFirstVertexSection.{u} n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap Δ[n] =
      𝟙 _ := by
  rw [← transportStandardFirstVertex_nerve]
  dsimp only [transportStandardFirstVertexSection]
  have h : nerveMap (transportStandardSection.{u} n) ≫
      nerveMap (transportStandardFirstVertex n) =
      nerveMap (transportStandardSection n ⋙ transportStandardFirstVertex n) := rfl
  rw [Category.assoc, ← Category.assoc (nerveMap _), h,
    transportStandardSection_firstVertex]
  change (stdSimplex.isoNerve n).hom ≫ 𝟙 _ ≫ (stdSimplex.isoNerve n).inv = 𝟙 _
  simp

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
