module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportSectionsRetraction

/-!
概要：元の射影の切断空間は strict transport 図式の通常の極限である。
方針：互換な under 圏の族の組み立てと制限の両逆関係から極限の普遍性を構成する。
規約：元の射影に left fibration 性は要求せず、通常の極限として述べる。
使われ方：Kerodon 5.3.1.5（Tag 035J）、7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の strict transport と切断模型の接続。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
variable {I : Type u} [SmallCategory I] {E : SSet.{u}}

/-- 概要：under 圏の射列は始点の標準持ち上げを最初の構造射で前合成して復元できる。
方針：under の三角形の可換性と忘却関手の忠実性を使う。
規約：始点の対象は射列の零番目の対象。
使われ方：Kerodon 5.3.4.7（Tag 026D）、7.4.1.6（Tag 05QS） の制限した族の回収。 -/
lemma scaffoldUnderChain_under_map {i : I} {n : ℕ} (τ : ComposableArrows (Under i) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain (τ ⋙ Under.forget i) ⋙ Under.map (τ.obj 0).hom = τ := by
  refine CategoryTheory.Functor.ext (fun k => ?_) ?_
  · change Under.mk ((τ.obj 0).hom ≫ (τ.map (homOfLE (Fin.zero_le k))).right) = τ.obj k
    exact congrArg Under.mk (Under.w (τ.map (homOfLE (Fin.zero_le k))))
  · intro k l f
    apply (Under.forget i).map_injective
    simp
    rfl

/-- 概要：互換な strict transport の族を組み立てて under 圏へ制限すると元の成分を評価する。
方針：始点の構造射に沿う錐の可換性を使い、under 圏の元の射列を復元する。
規約：任意のパラメータを持つ通常の錐を扱う。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の通常の極限の射影との可換性。 -/
lemma strictTransportConeAssembly_restriction (p : E ⟶ nerve I)
    (c : Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p)) (i : I) :
    (nerveMap (Under.forget i) ▷ c.pt) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportConeAssembly p c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (c.π.app i) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨τ, a⟩
  let σ := τ ⋙ Under.forget i
  let b : (Δ[n] : SSet.{u}) ⟶ c.pt := SSet.yonedaEquiv.symm a
  let w : (Δ[n] : SSet.{u}) ⟶ nerve (Under (σ.obj 0)) :=
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain σ)
  have hc : c.π.app (σ.obj 0) =
      c.π.app i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p (nerveMap (Under.forget i))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap (τ.obj 0).hom) := (c.w (τ.obj 0).hom).symm
  have he : lift w (𝟙 (Δ[n] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (b ≫ c.π.app (σ.obj 0)) =
        lift (SSet.yonedaEquiv.symm τ) b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (c.π.app i) := by
    rw [hc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter]
    simp only [← Category.assoc]
    rw [lift_whiskerRight, lift_whiskerLeft, Category.id_comp]
    have hw : w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap (τ.obj 0).hom = SSet.yonedaEquiv.symm τ := by
      rw [SSet.yonedaEquiv_symm_comp]
      exact congrArg SSet.yonedaEquiv.symm (scaffoldUnderChain_under_map τ)
    rw [hw]
  change SSet.yonedaEquiv (lift w (𝟙 (Δ[n] : SSet.{u})) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (b ≫ c.π.app (σ.obj 0))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (c.π.app i)).app (Opposite.op ⦋n⦌) (τ, a)
  rw [he, SSet.yonedaEquiv_comp]
  congr 1
  apply Prod.ext
  · change (fst (nerve (Under i)) c.pt).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (lift (SSet.yonedaEquiv.symm τ) b)) = τ
    rw [← SSet.yonedaEquiv_comp, lift_fst, Equiv.apply_symm_apply]
  · change (snd (nerve (Under i)) c.pt).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (lift (SSet.yonedaEquiv.symm τ) b)) = a
    rw [← SSet.yonedaEquiv_comp, lift_snd]
    exact SSet.yonedaEquiv.apply_symm_apply a

/-- 概要：strict transport の錐から切断空間への射は各射影と可換である。
方針：成分を評価し、直積の二因子の写像を交換して組み立ての制限の式を使う。
規約：錐の射としての実際の可換性。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の極限の存在部分。 -/
lemma strictTransportConeSections_fac (p : E ⟶ nerve I)
    (c : Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p)) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportConeSections p c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsRestriction p i = c.π.app i := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p (nerveMap (Under.forget i))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsRestriction_evaluation]
  rw [← Category.assoc, whisker_exchange, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportConeSections, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift_evaluation,
    strictTransportConeAssembly_restriction]

/-- 概要：通常の錐の射は simplicial replacement への組み立てと可換。
方針：各底の射列の始点で錐の射の可換性と Yoneda の自然性を使う。
規約：図式は任意の単体集合値図式。
使われ方：Kerodon 5.3.2.1（Tag 035V）、7.4.1.6（Tag 05QS） の互換な族の組み立ての一意性。 -/
lemma coneReplacementMap_naturality {H : I ⥤ SSet.{u}} {c d : Cone H} (f : c ⟶ d) :
    (nerve I ◁ f.hom) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneReplacementMap d = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneReplacementMap c := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, a⟩
  change (⟨σ, SSet.yonedaEquiv.symm (f.hom.app (Opposite.op ⦋n⦌) a) ≫
    d.π.app (σ.obj 0)⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex H n) =
      ⟨σ, SSet.yonedaEquiv.symm a ≫ c.π.app (σ.obj 0)⟩
  rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, f.w]

/-- 概要：strict transport の錐の射は元の全空間への組み立てと可換。
方針：simplicial replacement への組み立ての自然性を scaffold への合成で移す。
規約：元の射影の充填性は不要。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断空間への射の一意性。 -/
lemma strictTransportConeAssembly_naturality (p : E ⟶ nerve I)
    {c d : Cone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p)} (f : c ⟶ d) :
    (nerve I ◁ f.hom) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportConeAssembly p d = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportConeAssembly p c := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportConeAssembly, ← Category.assoc, coneReplacementMap_naturality]
  rfl

/-- 概要：元の射影の切断空間は strict transport 図式の通常の極限錐を担う。
方針：互換な族を組み立てて極限射を作り、制限の回収と組み立ての自然性で普遍性を示す。
規約：任意の小圏上の任意の射影 p で成立し、left fibration 性は不要。
使われ方：Kerodon 5.3.1.5（Tag 035J）、7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の strict transport と切断の極限の同定。 -/
noncomputable def transportSectionsConeIsLimit (p : E ⟶ nerve I) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsCone p) where
  lift c := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportConeSections p c
  fac c i := strictTransportConeSections_fac p c i
  uniq c f hf := by
    let m : c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsCone p := { hom := f, w := hf }
    have he := strictTransportConeAssembly_naturality p m
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.strictTransportConeAssembly_sections] at he
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportConeSections, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift_evaluation]
    exact he

/-- 概要：strict transport 図式の選択された通常の極限は元の射影の切断空間と同型。
方針：切断空間の極限錐の普遍性と選択された極限の一意性を使う。
規約：単体集合の厳密な同型として述べる。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の strict な極限と切断模型の比較。 -/
noncomputable def transportLimitSectionsIso (p : E ⟶ nerve I) :
    limit (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p :=
  (limit.isLimit _).conePointUniqueUpToIso (transportSectionsConeIsLimit p)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
