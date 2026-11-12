module

public import SerrePositivity.KST.Spectra.CircleMappingComponents

/-!
概要：円の Kan 置換上で基本群の指定類を実現する実際の自己射。
方針：類の単体代表を球面の射へ移し、anodyne 単位に沿って延長する。
規約：整数の負の次数も扱い、自然数の次数射の選択との厳密な一致は要求しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。loop と次数移動の符号の実際の比較射。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SSet
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel

namespace SerrePositivity.KST.Spectra.CirclePower

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：円の Kan 置換の指定基本類を任意の基本群の元へ送る自己射の存在。
方針：選んだ単体代表の球面の射を anodyne な単位に沿って延長する。
規約：基本群全体の巡回性を使わない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。負の次数の実際の円の射。 -/
theorem exists_classMap (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup space.{u}.right 0 space.basepoint) :
    ∃ p : space.{u} ⟶ space.{u}, evaluateGenerator p = a := by
  obtain ⟨s, hs⟩ := Quotient.mk_surjective a
  let g : PointedSimplicialSet.circle.{u} ⟶ space.{u} :=
    (SphereSimplex.equiv space.{u} 1).symm s
  have hspace : J.rlp (terminal.from space.{u}.right) :=
    (SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance
  obtain ⟨p, hp⟩ := KanHomotopyExtension.exists_extension unit.{u}.right
    (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle.{u}) hspace g.right
  let pp : space.{u} ⟶ space.{u} := Under.homMk p (by
    calc
      space.{u}.hom ≫ p = (PointedSimplicialSet.circle.{u}.hom ≫ unit.right) ≫ p := by
        rw [Under.w unit]
      _ = PointedSimplicialSet.circle.{u}.hom ≫ g.right := by rw [Category.assoc, hp]
      _ = space.{u}.hom := Under.w g)
  have hpp : unit.{u} ≫ pp = g := Under.UnderMorphism.ext hp
  refine ⟨pp, ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex pp.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint pp)
    (SphereSimplex.equiv space.{u} 1 unit)) = a
  rw [← SphereSimplex.equiv_comp, hpp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk ((SphereSimplex.equiv space.{u} 1)
    ((SphereSimplex.equiv space.{u} 1).symm s)) = a
  rw [Equiv.apply_symm_apply]
  exact hs

/-- 概要：指定基本類を任意の基本群の元へ送る実際の自己射。
方針：anodyne 延長の存在証明から一つ選ぶ。
規約：選択の独立性は写像空間の成分で検査する。
使われ方：Goerss–Jardine I §7。符号反転の円の射の実構成。 -/
def classMap (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup space.{u}.right 0 space.basepoint) : space.{u} ⟶ space.{u} :=
  (exists_classMap a).choose

/-- 概要：選んだ自己射の指定基本類での評価は指定した元。
方針：選択の性質を取り出す。
規約：全ての基本群の元に対して成立する。
使われ方：Goerss–Jardine I §7。整数次数射の作用の計算。 -/
@[simp]
theorem evaluateGenerator_classMap (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup space.{u}.right 0 space.basepoint) :
    evaluateGenerator (classMap a) = a := (exists_classMap a).choose_spec

/-- 概要：円の Kan 置換上の整数次数の実際の自己射。
方針：指定基本類の整数冪を実現する自己射を取る。
規約：負の整数と零も含む。
使われ方：BF 1978 §2、Goerss–Jardine I §7。loop の符号反転。 -/
def integerPowerMap (z : ℤ) : space.{u} ⟶ space.{u} := classMap (generator ^ z)

/-- 概要：整数次数の自己射は指定基本類をその整数冪へ送る。
方針：指定類を実現する自己射の評価式を使う。
規約：群の乗法記法による整数冪。
使われ方：Goerss–Jardine I §7。写像空間への整数倍作用の計算。 -/
@[simp]
theorem evaluateGenerator_integerPowerMap (z : ℤ) :
    evaluateGenerator (integerPowerMap.{u} z) = generator ^ z := evaluateGenerator_classMap _

/-- 概要：整数次数射の前合成は任意の点つき Kan 値の射の指定類の像を整数冪へ送る。
方針：基本群への誘導写像の合成法則と整数冪の保存を使う。
規約：全整数 z。
使われ方：Goerss–Jardine I §7、BF 1978 §2。負の次数を含む loop の作用。 -/
theorem evaluateGenerator_integerPower {Y : PointedSimplicialSet.{u}} [KanComplex Y.right]
    (f : space.{u} ⟶ Y) (z : ℤ) :
    evaluateGenerator (integerPowerMap z ≫ f) = evaluateGenerator f ^ z := by
  unfold evaluateGenerator
  have h := DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (n := 0)
    (integerPowerMap.{u} z).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) f.right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (integerPowerMap z ≫ f))) generator
  exact h.trans (by
    rw [MonoidHom.comp_apply]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f)
      (evaluateGenerator (integerPowerMap z)) = _
    rw [evaluateGenerator_integerPowerMap, map_zpow])

end

end SerrePositivity.KST.Spectra.CirclePower
