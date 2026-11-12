module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
public import Mathlib.Data.Finset.Max

/-!
# 細分の最終頂点写像

概要：標準単体の細分から元の標準単体への自然な写像を構成する。
方針：非空有限鎖をその最大元へ送り、nerve と標準単体の同型を使う。
規約：Moss 2020 §3 の sd–Ex 構成。Segal 1974 Proposition 1.6 の対角模型の補助。
使われ方：id→Ex の単位と、その反復による有限極限を保つ置換の入口。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite
open PartialOrder
open scoped _root_.Simplicial

/--
概要：線形順序の非空有限鎖をその最大元へ送る単調写像。
方針：有限集合の最大元と包含に関する単調性を使う。
規約：Moss 2020 §3 の最終頂点写像の頂点上の式。
使われ方：細分された単体から元の単体への写像。
-/
def finiteChainMaximum {α : Type u} [LinearOrder α] : NonemptyFiniteChains α →o α where
  toFun s := s.finset.max' s.nonempty
  monotone' a _b h := Finset.max'_subset a.nonempty h

/--
概要：非空有限鎖の最大元を取る操作は単調写像による像と可換である。
方針：単調写像は非空有限集合の最大元を保つ。
規約：Moss 2020 §3 の最終頂点写像の自然性。
使われ方：単体圏の任意の面・退化に関する整合。
-/
theorem finiteChainMaximum_map {α β : Type u} [LinearOrder α] [LinearOrder β]
    (f : α →o β) (s : NonemptyFiniteChains α) :
    finiteChainMaximum (s.map f) = f (finiteChainMaximum s) := by
  apply le_antisymm
  · apply Finset.max'_le _ (s.map f).nonempty
    intro b hb
    obtain ⟨a, ha, rfl⟩ := (NonemptyFiniteChains.mem_map_iff s f b).mp hb
    exact f.monotone (Finset.le_max' s.finset a ha)
  · exact Finset.le_max' _ _ ((NonemptyFiniteChains.mem_map_iff s f _).mpr
      ⟨s.finset.max' s.nonempty, Finset.max'_mem _ _, rfl⟩)

/--
概要：標準単体の細分から元の単体への最終頂点写像。
方針：有限鎖の最大元の単調写像に nerve を適用する。
規約：Moss 2020 §3。値の宇宙には ULift を使う。
使われ方：Ex への自然な包含を作る。
-/
def subdivisionLastVertexAt (n : SimplexCategory) :
    SimplexCategory.sd.{u}.obj n ⟶ SSet.stdSimplex.obj n :=
  nerveMap (finiteChainMaximum (α := ULift.{u} (Fin (n.len + 1)))).monotone.functor ≫
    (SSet.stdSimplex.isoNerve n.len).inv

/--
概要：最終頂点写像は単体圏に関して自然である。
方針：各頂点で有限鎖の最大元と単調写像の交換則を適用する。
規約：Moss 2020 §3。面と退化の双方を含む。
使われ方：id→Ex の次数間の自然性。
-/
theorem subdivisionLastVertex_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    SimplexCategory.sd.map f ≫ subdivisionLastVertexAt.{u} m =
      subdivisionLastVertexAt n ≫ SSet.stdSimplex.map f := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  let F : ULift.{u} (Fin (n.len + 1)) →o ULift.{u} (Fin (m.len + 1)) :=
    { toFun x := ULift.up (f x.down)
      monotone' _ _ h := f.toOrderHom.monotone h }
  let t : NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1))) := s.obj i
  change (finiteChainMaximum (t.map F)).down = f (finiteChainMaximum t).down
  exact congrArg ULift.down (finiteChainMaximum_map F t)

/--
概要：標準単体の細分上の自然な最終頂点変換。
方針：各次数の写像と任意の単調写像に関する自然性を束ねる。
規約：Moss 2020 §3 の Ex の単位を定める変換。
使われ方：単体的集合全体の id→Ex の構成。
-/
def subdivisionLastVertex : SimplexCategory.sd.{u} ⟶ SSet.stdSimplex where
  app := subdivisionLastVertexAt
  naturality _ _ f := subdivisionLastVertex_naturality f

/--
概要：頂点 i に、その頂点以下の全頂点からなる非空有限鎖を対応させる。
方針：有限な線形順序の初期区間を取る。
規約：Moss 2020 §3。単体ごとの切断に使い、単体圏に関する自然性は主張しない。
使われ方：最終頂点写像の全射性。
-/
def finiteChainInitialSegment (n : ℕ) :
    ULift.{u} (Fin (n + 1)) →o NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) where
  toFun i :=
    { finset := Finset.univ.filter (fun j => j ≤ i)
      nonempty := ⟨i, by simp⟩
      comparable a b := le_total a.val b.val }
  monotone' i j hij x hx := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans hij

/--
概要：初期区間の最大元は指定した頂点である。
方針：すべての元が頂点以下であり、頂点自身も区間に属する。
規約：Moss 2020 §3 の最終頂点写像の切断。
使われ方：単体ごとの右逆の計算。
-/
theorem finiteChainMaximum_initialSegment (n : ℕ) (i : ULift.{u} (Fin (n + 1))) :
    finiteChainMaximum (finiteChainInitialSegment n i) = i := by
  apply le_antisymm
  · apply Finset.max'_le _ (finiteChainInitialSegment n i).nonempty
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  · exact Finset.le_max' _ _ (by simp [finiteChainInitialSegment])

/--
概要：標準単体ごとの最終頂点写像の切断。
方針：頂点の初期区間を取る単調写像に nerve を適用する。
規約：Moss 2020 §3。単体圏のすべての射に関する切断の自然性は不要。
使われ方：最終頂点写像が epi であること。
-/
def subdivisionVertexSectionAt (n : SimplexCategory) :
    SSet.stdSimplex.{u}.obj n ⟶ SimplexCategory.sd.obj n :=
  (SSet.stdSimplex.isoNerve n.len).hom ≫
    nerveMap (finiteChainInitialSegment.{u} n.len).monotone.functor

/--
概要：単体ごとの初期区間による写像は最終頂点写像の右逆である。
方針：各単体の頂点で最大元と初期区間の計算をする。
規約：Moss 2020 §3 の Ex への包含の単射性に用いる。
使われ方：全射と単射の検証。
-/
@[reassoc] theorem subdivisionVertexSectionAt_lastVertex (n : SimplexCategory) :
    subdivisionVertexSectionAt.{u} n ≫ subdivisionLastVertexAt n = 𝟙 _ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  change (finiteChainMaximum (finiteChainInitialSegment n.len
    (ULift.up (SSet.stdSimplex.asOrderHom s i)))).down = SSet.stdSimplex.asOrderHom s i
  rw [finiteChainMaximum_initialSegment]

/--
概要：標準単体の最終頂点写像は epi である。
方針：明示した切断との合成が恒等であることを使う。
規約：Moss 2020 §3 の Ex の単位の単射性。
使われ方：前合成による Hom の単射性。
-/
instance subdivisionLastVertexAt_epi (n : SimplexCategory) : Epi (subdivisionLastVertexAt.{u} n) :=
  epi_of_epi_fac (subdivisionVertexSectionAt_lastVertex n)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
