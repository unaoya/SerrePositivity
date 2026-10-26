module
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphNativeSquare
public import SerrePositivity.InfinityCategories.Derived.DGCellResolvedGraphProjective
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransNerveHomTransport
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransTransport

/-!
概要：保存済み graph 比較を同じ実 Perf 関手間の native 全関手射として保持する。
方針：同じ bimodule 射の閉零成分と全 Hom 自然性を充満 Perf 部分圏へ制限する。
規約：元の解像度比較射を選び直さない。使われ方：実 Perf 延長比較族の自然性へ渡す元射。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories DGNerve
variable (R : Type u) [CommRing R] (B : Type (max (u + 1) v))
  [DGCategory R B] [Small.{u} B] (F G : DGFunctor R B B)
  (τ : DGFunctorParamTrans R B B (𝟙_ (Complex R)) F G)
local notation "P" => DGCategoryCellResolution.Source R B
local notation "Fp" => dgCellResolvedGraphPerfectFunctor R B F (dgCellResolvedGraph_projective R B F)
local notation "Gp" => dgCellResolvedGraphPerfectFunctor R B G (dgCellResolvedGraph_projective R B G)
local notation "m" => dgCellResolvedGraphMap R B F G τ
local notation "η" => dgBimoduleMapStrictNatTrans R (P) (P) (m)
local notation "J" => perfectDGModuleInclusion R (P) Set.univ

/-- 概要：同じ解像度比較射の実 Perf 関手間の厳密 dg 自然変換。
方針：同じ全次数の変換を充満部分圏へ制限する。規約：元閉零成分を保持。
使われ方：native Perf 全関手射の指定代表。 -/
def dgCellResolvedGraphPerfectStrictNatTrans : StrictNatTrans (Fp) (Gp) where
  app x := (η).app x
  naturality f := (η).naturality f

/-- 概要：同じ実 Perf 比較の包含像は元 bimodule 比較の全厳密変換。
方針：両関手の包含等号と同じ閉零成分を照合する。
規約：全単体の変換を保持。使われ方：元 native graph 射との同定。 -/
lemma dgCellResolvedGraphPerfectStrictNatTrans_inclusion :
    HEq (dgStrictNatTransPostcomp (dgCellResolvedGraphPerfectStrictNatTrans R B F G τ) (J)) (η) := by
  apply dgStrictNatTrans_heq_of_val
    (dgStrictNatTransPostcomp (dgCellResolvedGraphPerfectStrictNatTrans R B F G τ) (J)) (η)
    (dgCellResolvedGraphPerfectFunctor_inclusion R B F (dgCellResolvedGraph_projective R B F))
    (dgCellResolvedGraphPerfectFunctor_inclusion R B G (dgCellResolvedGraph_projective R B G))
  intro x
  rfl

/-- 概要：元 graph 比較の同じ実 Perf nerve 間の全関手射。
方針：保存済み比較の厳密変換を同じ nerve 作用で写す。
規約：可逆性を仮定しない。使われ方：共通 Perf 延長比較族の自然性。 -/
def dgCellResolvedGraphPerfectNerveArrow : FunctorHom (dgNerve.map (Fp)) (dgNerve.map (Gp)) :=
  dgStrictNatTransNerveHom R (P) (PerfectDGModule R (P))
    (dgCellResolvedGraphPerfectStrictNatTrans R B F G τ)

/-- 概要：同じ Perf 全射の包含後は元 bimodule 比較の全 native 射。
方針：全厳密変換の包含同定と nerve の後合成整合性を使う。
規約：頂点成分だけで代用しない。使われ方：native square と Perf 比較の接続。 -/
lemma dgCellResolvedGraphPerfectNerveArrow_inclusion :
    HEq (functorHomPostcomp (dgNerve.map (Fp)) (dgNerve.map (Gp)) (dgNerve.map (J))
      (dgCellResolvedGraphPerfectNerveArrow R B F G τ))
      ((dgBimoduleFunctorHomFunctor R (P) (P)).map (m)) := by
  have h := dgStrictNatTransNerveHom_postcomp_heq R (P) (PerfectDGModule R (P))
    (RightModule R (P)) (dgCellResolvedGraphPerfectStrictNatTrans R B F G τ) (J)
  have k := dgStrictNatTransNerveHom_heq R (P) (RightModule R (P))
    (dgStrictNatTransPostcomp (dgCellResolvedGraphPerfectStrictNatTrans R B F G τ) (J)) (η)
    (dgCellResolvedGraphPerfectFunctor_inclusion R B F (dgCellResolvedGraph_projective R B F))
    (dgCellResolvedGraphPerfectFunctor_inclusion R B G (dgCellResolvedGraph_projective R B G))
    (dgCellResolvedGraphPerfectStrictNatTrans_inclusion R B F G τ)
  exact h.symm.trans k

end SerrePositivity.KST.SConstruction
