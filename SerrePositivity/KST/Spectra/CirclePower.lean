module

public import SerrePositivity.KST.Spectra.SphereSimplex
public import SerrePositivity.KST.Spectra.PointedKanReplacement

/-!
概要：円の Kan 置換に、指定した基本類の自然数倍を実現する自己射を作る。
方針：基本群の積の代表を球面の射へ戻し、anodyne な Kan 置換単位に沿って延長する。
規約：ここで計算するのは指定基本類の像。高次写像空間での作用は後続部分。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）、BF 1978 §2。有理 telescope の乗法射。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SSet
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.CirclePower

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：単体的な円の点つき Kan 置換。
方針：ホーンの小対象論法による既存の Kan 置換を使う。
規約：元の円との比較は anodyne な単位。
使われ方：BF 1978 §2。有理化用の自己射を実現する源。 -/
abbrev space : PointedSimplicialSet.{u} := PointedKanReplacement.obj PointedSimplicialSet.circle.{u}

/-- 概要：円の置換の基礎単体集合は Kan。
方針：点つき Kan 置換の性質を使う。
規約：元の円の Kan 性を要求しない。
使われ方：Goerss–Jardine I §7。基本群の積の代表の存在。 -/
instance space_kanComplex : KanComplex space.{u}.right :=
  PointedKanReplacement.obj_kanComplex _

/-- 概要：元の円から Kan 置換への標準射。
方針：点つき Kan 置換の単位を使う。
規約：点つき射。
使われ方：Goerss–Jardine I §7。指定した基本類の球面の代表。 -/
def unit : PointedSimplicialSet.circle.{u} ⟶ space.{u} :=
  PointedKanReplacement.unit.app _

/-- 概要：円の Kan 置換単位が定める基本群の指定類。
方針：球面の射を境界定数一次単体へ戻して商を取る。
規約：基本群全体が巡回であることはここでは仮定しない。
使われ方：Kerodon §3.2.3（Tag 00W3）、Goerss–Jardine I §7。自己射に送らせる基準の類。 -/
def generator : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup space.{u}.right 0 space.{u}.basepoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SphereSimplex.equiv space.{u} 1 unit.{u})

/-- 概要：指定類の自然数 m 乗を表す境界定数一次単体を選ぶ。
方針：商の標準射の全射性を使う。
規約：群は乗法記法。整数の加法的 m 倍に対応する。
使われ方：Kerodon §3.2.3（Tag 00W3）。実際の球面の射へ戻す代表。 -/
def representative (m : ℕ) : space.{u}.right.PtSimplex 1 space.{u}.basepoint :=
  Classical.choose (show ∃ s : space.{u}.right.PtSimplex 1 space.{u}.basepoint,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = generator.{u} ^ m from Quotient.mk_surjective _)

/-- 概要：選んだ一次単体の類は指定類の m 乗。
方針：商の代表の選択の性質を取り出す。
規約：全自然数 m。
使われ方：Goerss–Jardine I §7。自己射の指定基本類での計算。 -/
theorem representative_class (m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (representative.{u} m) = generator.{u} ^ m :=
  Classical.choose_spec (show ∃ s : space.{u}.right.PtSimplex 1 space.{u}.basepoint,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = generator.{u} ^ m from Quotient.mk_surjective _)

/-- 概要：指定基本類の m 乗の代表を円からの点つき射にする。
方針：境界を潰す球面の普遍性を使う。
規約：Kan 置換前の円を源とする。
使われ方：Goerss–Jardine I §7。anodyne 単位に沿って延長する入力。 -/
def sphereMap (m : ℕ) : PointedSimplicialSet.circle.{u} ⟶ space.{u} :=
  (SphereSimplex.equiv space.{u} 1).symm (representative m)

/-- 概要：指定した円からの射は Kan 置換上の点つき自己射へ延長できる。
方針：anodyne な単位に沿う Kan 値の延長を取り、基点保存を元の円から回収する。
規約：延長は厳密に単位との合成を保つ。
使われ方：Goerss–Jardine I §7、BF 1978 §2。実際の乗法射の存在。 -/
theorem exists_powerMap (m : ℕ) : ∃ p : space.{u} ⟶ space.{u}, unit ≫ p = sphereMap m := by
  have hspace : J.rlp (terminal.from space.{u}.right) :=
    (SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance
  obtain ⟨p, hp⟩ := KanHomotopyExtension.exists_extension unit.{u}.right
    (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle.{u}) hspace (sphereMap m).right
  let pp : space.{u} ⟶ space.{u} := Under.homMk p (by
    calc
      space.{u}.hom ≫ p = (PointedSimplicialSet.circle.{u}.hom ≫ unit.right) ≫ p := by
        rw [Under.w unit]
      _ = PointedSimplicialSet.circle.{u}.hom ≫ (sphereMap m).right := by
        rw [Category.assoc, hp]
      _ = space.{u}.hom := Under.w (sphereMap m))
  exact ⟨pp, Under.UnderMorphism.ext hp⟩

/-- 概要：円の Kan 置換上の、指定基本類を m 乗へ送る自己射。
方針：anodyne 単位に沿う延長を一つ選ぶ。
規約：後続の写像空間の作用の証明に使う実際の点つき射。
使われ方：BF 1978 §2。有理化の乗法列の構成材料。 -/
def powerMap (m : ℕ) : space.{u} ⟶ space.{u} := (exists_powerMap.{u} m).choose

/-- 概要：選んだ自己射を元の円へ制限すると指定した m 乗の代表になる。
方針：延長の選択の性質を使う。
規約：点つき射の厳密な等式。
使われ方：Goerss–Jardine I §7。基本類での自己射の計算。 -/
theorem unit_powerMap (m : ℕ) : unit.{u} ≫ powerMap m = sphereMap m :=
  (exists_powerMap m).choose_spec

/-- 概要：円の Kan 置換の自己射は指定基本類を m 乗へ送る。
方針：元の円への制限と球面・単体の同値の自然性で計算する。
規約：他の群の元や高次写像空間への作用の主張は後続部分。
使われ方：Kerodon §3.2.3（Tag 00W3）、BF 1978 §2。有理化用の自己射の指定基本類での検証。 -/
theorem powerMap_generator (m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (powerMap.{u} m).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
      generator = generator ^ m := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (powerMap m).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
    (SphereSimplex.equiv space.{u} 1 unit)) = _
  rw [← SphereSimplex.equiv_comp, unit_powerMap]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk ((SphereSimplex.equiv space.{u} 1)
    ((SphereSimplex.equiv space.{u} 1).symm (representative m))) = _
  rw [Equiv.apply_symm_apply, representative_class]

/-- 概要：円の Kan 置換からの点つき射を指定基本類の像で評価する。
方針：基本群の誘導準同型を指定類へ適用する。
規約：標的 Y は Kan。評価の単射性・全射性はここでは主張しない。
使われ方：Goerss–Jardine I §7。円の自己射の後合成における計算。 -/
def evaluateGenerator {Y : PointedSimplicialSet.{u}} [KanComplex Y.right]
    (f : space.{u} ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right 0 Y.basepoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f) generator

/-- 概要：円の自己射による前合成は、指定基本類の像を m 乗へ送る。
方針：誘導準同型の合成法則と群の冪の保存を使う。
規約：任意の Kan 値の点つき射 f について計算する。
使われ方：Kerodon §3.2.3（Tag 00W3）、BF 1978 §2。有理 telescope の自己射の検証の基礎。 -/
theorem evaluateGenerator_power {Y : PointedSimplicialSet.{u}} [KanComplex Y.right]
    (f : space.{u} ⟶ Y) (m : ℕ) :
    evaluateGenerator (powerMap m ≫ f) = evaluateGenerator f ^ m := by
  unfold evaluateGenerator
  have h := DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (n := 0)
    (powerMap.{u} m).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) f.right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (powerMap m ≫ f)))
      generator
  exact h.trans (by rw [MonoidHom.comp_apply, powerMap_generator, MonoidHom.map_pow])

end

end SerrePositivity.KST.Spectra.CirclePower
