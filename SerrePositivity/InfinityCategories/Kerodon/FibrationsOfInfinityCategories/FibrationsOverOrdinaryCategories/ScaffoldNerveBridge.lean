module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldSimplexBridge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteTail
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-!
概要：有限鎖の nerve の最初の辺と尾部を貼るための錐の比較。
方針：始対象の頂点包含と join の相対境界を使い、有限鎖の nerve に移す。
規約：有限順序は ULift で係数と同じ宇宙に置く。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、有限鎖上の scaffold の帰納段階。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：有限鎖の nerve に新しい始点を加える錐の標準同型。
方針：標準単体との同型を join の右因子に適用する。
規約：尾部は n+1 頂点、全体は n+2 頂点。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、尾部の錐と全体の同一視。 -/
noncomputable def scaffoldFiniteNerveConeIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (nerve (ULift.{u} (Fin (n + 1)))) ≅
      nerve (ULift.{u} (Fin (n + 2))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightFunctor Δ[0]).mapIso (stdSimplex.isoNerve n).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n ≪≫ stdSimplex.isoNerve (n + 1)

/-- 概要：零番目の面写像は有限鎖の尾部への包含の nerve に対応する。
方針：各射列の頂点を計算し、順序圏の射の一意性を使う。
規約：面写像は最初の頂点を除く δ₀。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、標準単体と有限鎖の貼り合わせの整合性。 -/
lemma scaffoldFiniteTail_isoNerve (n : ℕ) :
    stdSimplex.δ (0 : Fin (n + 2)) ≫ (stdSimplex.isoNerve.{u} (n + 1)).hom =
      (stdSimplex.isoNerve n).hom ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n) := by
  ext d s i
  change (Δ[n] _⦋d.unop.len⦌ : Type u) at s
  change ((0 : Fin (n + 2)).succAbove (s i)).val = (s i).succ.val
  rw [Fin.succAbove_zero]

/-- 概要：有限鎖の錐の右包含は尾部への包含になる。
方針：標準単体の錐の右包含と尾部の面写像の式を合成する。
規約：同型の順方向で比較する。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、尾部の simplicial replacement との接続。 -/
lemma scaffoldFiniteNerveConeIso_inr (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (nerve (ULift.{u} (Fin (n + 1)))) ≫
        (scaffoldFiniteNerveConeIso n).hom = nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.isoNerve n).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫ (stdSimplex.isoNerve (n + 1)).hom) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc, ← Category.assoc
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[n]), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso_inr,
    scaffoldFiniteTail_isoNerve, Iso.inv_hom_id_assoc]

/-- 概要：有限鎖の尾部の最初の頂点からの包含は left anodyne。
方針：零頂点が始対象であることに nerve の一般補題を使う。
規約：n=0 の場合も含む。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、最初の辺と尾部の比較の入力。 -/
lemma scaffoldFiniteNervePoint_leftAnodyne (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint_leftAnodyne (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial n)

/-- 概要：最初の辺と有限鎖の尾部から尾部の錐への比較。
方針：辺を二頂点の join に戻し、尾部の最初の頂点に沿って貼る。
規約：共通の頂点は辺の終点と尾部の零頂点。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、有限鎖の比較の中間表示。 -/
noncomputable def scaffoldNerveConeBridge (n : ℕ) :
    pushout (stdSimplex.δ (0 : Fin 2))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (nerve (ULift.{u} (Fin (n + 1)))) :=
  pushout.desc
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up 0)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] _) (by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldIntervalCone_endpoint, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap])

/-- 概要：有限鎖の錐への比較は inner anodyne。
方針：始対象の頂点包含の left anodyne 性を join の相対境界に適用する。
規約：pushout の区間表示と二頂点の join 表示を同型で移す。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、有限鎖の全体への拡張。 -/
lemma scaffoldNerveConeBridge_innerAnodyne (n : ℕ) :
    innerAnodyneExtensions (scaffoldNerveConeBridge.{u} n) := by
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)
  have hp : IsPushout (stdSimplex.δ (0 : Fin 2)) i
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[0]) i)
      (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[0]) i) := by
    apply (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[0]) i).of_iso
      (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0) (Iso.refl _) (Iso.refl _)
    · simpa only [Iso.refl_hom, Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldIntervalCone_inr.{u}
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  have he : scaffoldNerveConeBridge n = hp.isoPushout.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap i Δ[0] := by
    apply pushout.hom_ext
    · rw [scaffoldNerveConeBridge, pushout.inl_desc, ← Category.assoc,
        hp.inl_isoPushout_inv, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap_join]
    · rw [scaffoldNerveConeBridge, pushout.inr_desc, ← Category.assoc,
        hp.inr_isoPushout_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap_right]
  rw [he, innerAnodyneExtensions.cancel_left_of_respectsIso]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightBoundaryMap_innerAnodyne_of_leftAnodyne i Δ[0]
    (scaffoldFiniteNervePoint_leftAnodyne n)

/-- 概要：最初の辺と有限鎖の尾部から全体の nerve への比較。
方針：尾部の錐への比較に有限鎖の錐の同型を合成する。
規約：標的は n+2 頂点の有限鎖の nerve。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、最初の係数を持つ部分の比較。 -/
noncomputable def scaffoldFiniteNerveBridge (n : ℕ) :
    pushout (stdSimplex.δ (0 : Fin 2))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) ⟶
      nerve (ULift.{u} (Fin (n + 2))) :=
  scaffoldNerveConeBridge n ≫ (scaffoldFiniteNerveConeIso n).hom

/-- 概要：有限鎖の最初の辺と尾部の比較は inner anodyne。
方針：錐への比較の性質を標的の同型で移す。
規約：有限鎖のすべての長さで成立する。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、円柱から全体への比較の帰納段階。 -/
lemma scaffoldFiniteNerveBridge_innerAnodyne (n : ℕ) :
    innerAnodyneExtensions (scaffoldFiniteNerveBridge.{u} n) := by
  rw [scaffoldFiniteNerveBridge, innerAnodyneExtensions.cancel_right_of_respectsIso]
  exact scaffoldNerveConeBridge_innerAnodyne n

/-- 概要：有限鎖の比較は任意の係数との積を取っても inner anodyne。
方針：inner anodyne な射の積による保存を使う。
規約：係数の Kan 性は要求しない。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、simplicial replacement の係数付き部分。 -/
lemma scaffoldFiniteNerveBridge_whiskerRight_innerAnodyne (n : ℕ) (K : SSet.{u}) :
    innerAnodyneExtensions (scaffoldFiniteNerveBridge n ▷ K) :=
  (scaffoldFiniteNerveBridge_innerAnodyne n).whiskerRight K

/-- 概要：有限鎖の比較を尾部に制限すると標準の包含を回収する。
方針：pushout の計算則と錐の右包含の整合性を使う。
規約：尾部は pushout の右因子。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、尾部の replacement との貼り合わせ。 -/
lemma scaffoldFiniteNerveBridge_inr (n : ℕ) :
    pushout.inr (stdSimplex.δ (0 : Fin 2))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _)) ≫
      scaffoldFiniteNerveBridge n = nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n) := by
  rw [scaffoldFiniteNerveBridge, scaffoldNerveConeBridge, ← Category.assoc,
    pushout.inr_desc, scaffoldFiniteNerveConeIso_inr]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
