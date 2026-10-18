module

public import SerrePositivity.KST.Comparison.FatRealizationDesc

/-!
# fat realization の関手性

概要：二重単体集合の射を fat realization の射へ送り、対角への比較を自然変換にする。
方針：面の関係式への自然性から各行の写像を余等化子へ降ろす。
規約：Segal 1974 Proposition 1.6、Appendix A の具体的な模型。
使われ方：有限骨格の帰納における元の射と模型の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial
open SerrePositivity.BisimplicialModel

/--
概要：二重単体集合の射が誘導する fat realization の射。
方針：各行の写像に終域の包含を合成し、面の関係式へ自然性を適用する。
規約：単射の面についてのみ関係式を確認する。
使われ方：fat realization の関手の射。
-/
def fatRealizationMap {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G) :
    fatRealization F ⟶ fatRealization G :=
  fatRealizationDesc F
    (fun n => (α.app (op ⦋n⦌) ▷ Δ[n]) ≫ fatRealizationInclusion G n) (by
      intro θ
      apply NatTrans.ext
      funext d
      apply ConcreteCategory.hom_ext
      intro p
      have hα := congrArg (fun t => t.app d p.1) (α.naturality θ.hom.op)
      calc
        _ = (fatRealizationInclusion G θ.source).app d
            ((G.map θ.hom.op).app d ((α.app (op ⦋θ.target⦌)).app d p.1), p.2) :=
          congrArg (fun y => (fatRealizationInclusion G θ.source).app d (y, p.2)) hα
        _ = _ := congrArg (fun t => t.app d ((α.app (op ⦋θ.target⦌)).app d p.1, p.2))
          (fatRealizationInclusion_face G θ))

/--
概要：fat realization の射の各行への制限は元の自然変換の成分から得られる。
方針：desc の計算則を使う。
規約：行と標準単体の積を介する等式。
使われ方：恒等・合成の計算と対角比較の自然性。
-/
@[reassoc] theorem fatRealizationInclusion_map
    {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G) (n : ℕ) :
    fatRealizationInclusion F n ≫ fatRealizationMap α =
      (α.app (op ⦋n⦌) ▷ Δ[n]) ≫ fatRealizationInclusion G n :=
  fatRealizationInclusion_desc F _ _ n

/--
概要：二重単体集合から fat realization を取る関手。
方針：恒等と合成を各行への制限の一意性で証明する。
規約：射の定義に局所化を使わない実際の関手。
使われ方：骨格の図式と対角模型を比較する。
-/
def fatRealizationFunctor : (SimplexCategoryᵒᵖ ⥤ SSet.{u}) ⥤ SSet.{u} where
  obj := fatRealization
  map := fatRealizationMap
  map_id F := by
    apply fatRealization_hom_ext
    intro n
    rw [fatRealizationInclusion_map]
    simp
  map_comp α β := by
    apply fatRealization_hom_ext
    intro n
    simp only [fatRealizationInclusion_map, fatRealizationInclusion_map_assoc,
      NatTrans.comp_app, comp_whiskerRight, Category.assoc]

/--
概要：fat realization から対角への比較は自然である。
方針：各行へ制限し、元の行の評価の自然性を使う。
規約：比較写像の可逆性はここでは主張しない。
使われ方：有限骨格の帰納の結論を対角模型へ移す比較。
-/
def fatRealizationToDiagonalNatTrans : fatRealizationFunctor.{u} ⟶ diagonal where
  app := fatRealizationToDiagonal
  naturality {F G} α := by
    apply fatRealization_hom_ext
    intro n
    change fatRealizationInclusion F n ≫ (fatRealizationMap α ≫ fatRealizationToDiagonal G) =
      fatRealizationInclusion F n ≫ (fatRealizationToDiagonal F ≫ diagonal.map α)
    simp only [fatRealizationInclusion_map_assoc, fatRealizationInclusion_toDiagonal,
      fatRealizationInclusion_toDiagonal_assoc]
    exact diagonalRowEvaluation_naturality α n

end SerrePositivity.KST.Comparison
