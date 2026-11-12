module
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphNativeAugmentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleResolvedMapInvertible

/-!
概要：元 graph 比較の増大 square を native 全関手圏の射として可換にする。
方針：実 nerve の全関手射を準同型反転後に導来 bimodule 圏へ降ろし、元の射を回収する。
規約：導来 bimodule 等号だけを結論にせず、同じ native 全射を固定する。
使われ方：中央射の二成分の増大比較の coherence。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (B : Type (max (u + 1) v))
  [DGCategory R B] [Small.{u} B]
local notation "P" => DGCategoryCellResolution.Source R B
local notation "ρ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R (P)) (P)
  (DGFunctor.id (RightModule R (P)))

/-- 概要：同じ cell 上の実 bimodule を native 導来加群値の全関手へ送る。
方針：元実 nerve 全関手と実加群分解の後合成を使う。
規約：元の全自然変換の射を保持。使われ方：graph 増大 square の実値域。 -/
def dgCellGraphNativeFunctor : BimoduleCategory R (P) (P) ⥤
    hoFunctor.obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (P))).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R (P))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R (P) (P) ⋙
    SSet.mapHomotopyCategory ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (P))).map (ρ))

/-- 概要：同じ native 全関手作用は各実 bimodule 準同型を反転する。
方針：元の全自然な実変換の点ごとの準同型性を使う。
規約：全関手圏での可逆性。使われ方：同じ射作用の指定局所化への下降。 -/
lemma dgCellGraphNativeFunctor_inverts :
    (BimoduleCategory.quasiIso R (P) (P)).IsInvertedBy (dgCellGraphNativeFunctor R B) := by
  intro X Y f hf
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor_resolvedMap_isIso_of_quasiIso R (P) (P) f hf

/-- 概要：保存済み graph 比較の同じ増大 square は native 全関手射として可換。
方針：元全関手作用の局所化から元の射を厳密に回収する。
規約：対象別成分・導来 bimodule 等号だけへの弱化なし。
使われ方：元比較と解像度比較の二縦辺の全自然性。 -/
lemma dgCellResolvedGraphNativeSquare (F G : DGFunctor R B B)
    (τ : DGFunctorParamTrans R B B (𝟙_ (Complex R)) F G) :
    (dgCellGraphNativeFunctor R B).map (dgCellResolvedGraphMap R B F G τ) ≫
        (dgCellGraphNativeFunctor R B).map (dgCellResolvedGraphResolution R B G).π =
      (dgCellGraphNativeFunctor R B).map (dgCellResolvedGraphResolution R B F).π ≫
        (dgCellGraphNativeFunctor R B).map (dgCellRestrictedGraphMap R B F G τ) := by
  let J := bimoduleToDerived R (P) (P)
  let N := dgCellGraphNativeFunctor R B
  let L := bimoduleDerivedLift R (P) (P) N (dgCellGraphNativeFunctor_inverts R B)
  let e : J ⋙ L ≅ N :=
    eqToIso (bimoduleDerivedLift_fac R (P) (P) N (dgCellGraphNativeFunctor_inverts R B))
  let a := dgCellResolvedGraphMap R B F G τ ≫ (dgCellResolvedGraphResolution R B G).π
  let b := (dgCellResolvedGraphResolution R B F).π ≫ dgCellRestrictedGraphMap R B F G τ
  have h : J.map a = J.map b := by
    exact (J.map_comp _ _).trans
      ((dgCellResolvedGraphMap_fac R B F G τ).trans (J.map_comp _ _).symm)
  have hL := congrArg L.map h
  have ha := e.hom.naturality a
  have hb := e.hom.naturality b
  change L.map (J.map a) ≫ _ = _ at ha
  change L.map (J.map b) ≫ _ = _ at hb
  rw [hL] at ha
  have hn : N.map a = N.map b := (cancel_epi (e.hom.app _)).1 (ha.symm.trans hb)
  exact (N.map_comp _ _).symm.trans (hn.trans (N.map_comp _ _))

end SerrePositivity.KST.SConstruction
