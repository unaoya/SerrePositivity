import SerrePositivity.KST.SConstruction

/-!
概要：S• 構成の公開宣言の型と公理を監査する。
方針：型の検査と公理一覧を各宣言について出力する。
規約：propext・Classical.choice・Quot.sound のみ許可。
使われ方：BGT §7 に対応する保存単位の検証。
-/

#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion
#check @SerrePositivity.KST.SConstruction.arCofiberCompletion
#print axioms SerrePositivity.KST.SConstruction.arCofiberCompletion
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_boundary
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_boundary
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily_isCofiber
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily_isCofiber
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_vertex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_vertex
#check @SerrePositivity.KST.SConstruction.IsGapped.arCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.IsGapped.arCofiberFamily_vertex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_ι
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_ι
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_apex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_apex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_apex
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_apex
#check @SerrePositivity.KST.SConstruction.intervalStep_mono_endpoints
#print axioms SerrePositivity.KST.SConstruction.intervalStep_mono_endpoints
#check @SerrePositivity.KST.SConstruction.arCofiberSquareOrder
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareOrder
#check @SerrePositivity.KST.SConstruction.arCofiberSquareChain
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareChain
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_at
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_at
#check @SerrePositivity.KST.SConstruction.curry_vertex_value
#print axioms SerrePositivity.KST.SConstruction.curry_vertex_value
#check @SerrePositivity.KST.SConstruction.arCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamily
#check @SerrePositivity.KST.SConstruction.arCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamily_vertex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamily
#check @SerrePositivity.KST.SConstruction.curry_evaluate_vertex
#print axioms SerrePositivity.KST.SConstruction.curry_evaluate_vertex
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_apex
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_apex
#check @SerrePositivity.KST.SConstruction.arCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamily_apex
#check @SerrePositivity.KST.SConstruction.cofiberApex
#print axioms SerrePositivity.KST.SConstruction.cofiberApex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamily_apex
#check @SerrePositivity.KST.SConstruction.arCofiberInputOrder
#print axioms SerrePositivity.KST.SConstruction.arCofiberInputOrder
#check @SerrePositivity.KST.SConstruction.arCofiberInputMap
#print axioms SerrePositivity.KST.SConstruction.arCofiberInputMap
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_bottom
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_bottom
#check @SerrePositivity.KST.SConstruction.frameCofiberInputOperator
#print axioms SerrePositivity.KST.SConstruction.frameCofiberInputOperator
#check @SerrePositivity.KST.SConstruction.frameCofiberInputs
#print axioms SerrePositivity.KST.SConstruction.frameCofiberInputs
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_input
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_input
#check @SerrePositivity.KST.SConstruction.gappedFrameRestriction_ι
#print axioms SerrePositivity.KST.SConstruction.gappedFrameRestriction_ι
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_input
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_input
#check @SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex
#print axioms SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex
#check @SerrePositivity.KST.SConstruction.cofiberDiagrams
#print axioms SerrePositivity.KST.SConstruction.cofiberDiagrams
#check @SerrePositivity.KST.SConstruction.cofiberProjection
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection
#check @SerrePositivity.KST.SConstruction.cofiberForgetZero
#print axioms SerrePositivity.KST.SConstruction.cofiberForgetZero
#check @SerrePositivity.KST.SConstruction.cofiberForgetZero_ι
#print axioms SerrePositivity.KST.SConstruction.cofiberForgetZero_ι
#check @SerrePositivity.KST.SConstruction.cofiberZeroArrow
#print axioms SerrePositivity.KST.SConstruction.cofiberZeroArrow
#check @SerrePositivity.KST.SConstruction.cofiberZeroArrow_ι
#print axioms SerrePositivity.KST.SConstruction.cofiberZeroArrow_ι
#check @SerrePositivity.KST.SConstruction.cofiberZeroArrow_source
#print axioms SerrePositivity.KST.SConstruction.cofiberZeroArrow_source
#check @SerrePositivity.KST.SConstruction.pushoutProjection_bottom
#print axioms SerrePositivity.KST.SConstruction.pushoutProjection_bottom
#check @SerrePositivity.KST.SConstruction.cofiberProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.exists_relative_cofiberFamily
#print axioms SerrePositivity.KST.SConstruction.exists_relative_cofiberFamily
#check @SerrePositivity.KST.SConstruction.cofiberFamilySpace
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySpace
#check @SerrePositivity.KST.SConstruction.cofiberFamilySpace_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySpace_isContractibleKan
#check @SerrePositivity.KST.SConstruction.cofiberFamiliesIso
#print axioms SerrePositivity.KST.SConstruction.cofiberFamiliesIso
#check @SerrePositivity.KST.SConstruction.cofiberSection
#print axioms SerrePositivity.KST.SConstruction.cofiberSection
#check @SerrePositivity.KST.SConstruction.cofiberSection_projection
#print axioms SerrePositivity.KST.SConstruction.cofiberSection_projection
#check @SerrePositivity.KST.SConstruction.cofiberFunctor
#print axioms SerrePositivity.KST.SConstruction.cofiberFunctor
#check @SerrePositivity.KST.SConstruction.arSquare_cofiber_zero_corner
#print axioms SerrePositivity.KST.SConstruction.arSquare_cofiber_zero_corner
#check @SerrePositivity.KST.SConstruction.gappedCofiberTriangle
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberTriangle
#check @SerrePositivity.KST.SConstruction.gappedCofiberTriangle_isCofiber
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberTriangle_isCofiber
#check @SerrePositivity.KST.SConstruction.firstRowNerve
#print axioms SerrePositivity.KST.SConstruction.firstRowNerve
#check @SerrePositivity.KST.SConstruction.firstRowOrder
#print axioms SerrePositivity.KST.SConstruction.firstRowOrder
#check @SerrePositivity.KST.SConstruction.firstRowInclusion
#print axioms SerrePositivity.KST.SConstruction.firstRowInclusion
#check @SerrePositivity.KST.SConstruction.firstRowRestriction
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction
#check @SerrePositivity.KST.SConstruction.gappedDiagram
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram
#check @SerrePositivity.KST.SConstruction.gappedDiagram_isGapped
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_isGapped
#check @SerrePositivity.KST.SConstruction.firstRowRestriction_vertex
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_vertex
#check @SerrePositivity.KST.SConstruction.firstRowSimplexIso
#print axioms SerrePositivity.KST.SConstruction.firstRowSimplexIso
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData
#check @SerrePositivity.KST.SConstruction.firstRowCofiberData
#print axioms SerrePositivity.KST.SConstruction.firstRowCofiberData
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_boundary
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_boundary
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_isGapped_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_isGapped_of_vertexSurjective
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_ι
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_ι
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_boundary
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_boundary
#check @SerrePositivity.KST.SConstruction.boundary_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.boundary_vertex_surjective
#check @SerrePositivity.KST.SConstruction.exists_gappedBoundaryFilling_of_firstRowFilling
#print axioms SerrePositivity.KST.SConstruction.exists_gappedBoundaryFilling_of_firstRowFilling
#check @SerrePositivity.KST.SConstruction.frame_extend_boundary
#print axioms SerrePositivity.KST.SConstruction.frame_extend_boundary
#check @SerrePositivity.KST.SConstruction.firstRowFrameOrder
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameOrder
#check @SerrePositivity.KST.SConstruction.firstRowFrameMap
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameMap
#check @SerrePositivity.KST.SConstruction.frameRowChain_positive
#print axioms SerrePositivity.KST.SConstruction.frameRowChain_positive
#check @SerrePositivity.KST.SConstruction.frameRowChainInverse
#print axioms SerrePositivity.KST.SConstruction.frameRowChainInverse
#check @SerrePositivity.KST.SConstruction.frameFirstRowMap
#print axioms SerrePositivity.KST.SConstruction.frameFirstRowMap
#check @SerrePositivity.KST.SConstruction.firstRowFrameMap_comp
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameMap_comp
#check @SerrePositivity.KST.SConstruction.frameFirstRowMap_comp
#print axioms SerrePositivity.KST.SConstruction.frameFirstRowMap_comp
#check @SerrePositivity.KST.SConstruction.frameFirstRowIso
#print axioms SerrePositivity.KST.SConstruction.frameFirstRowIso
#check @SerrePositivity.KST.SConstruction.simplexFirstVertex_stdSimplex_of_notMem_boundary
#print axioms SerrePositivity.KST.SConstruction.simplexFirstVertex_stdSimplex_of_notMem_boundary
#check @SerrePositivity.KST.SConstruction.initialBoundaryLifting_ihom_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.initialBoundaryLifting_ihom_of_pointwise
#check @SerrePositivity.KST.SConstruction.isInitialVertex_functorVertex_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isInitialVertex_functorVertex_of_pointwise
#check @SerrePositivity.KST.SConstruction.isZeroVertex_functorVertex_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_functorVertex_of_pointwise
#check @SerrePositivity.KST.SConstruction.isZeroVertex_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_of_pointwise
#check @SerrePositivity.KST.SConstruction.evaluateFunctorCocone
#print axioms SerrePositivity.KST.SConstruction.evaluateFunctorCocone
#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone
#check @SerrePositivity.KST.SConstruction.initialBoundaryLifting_coconeRestriction_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.initialBoundaryLifting_coconeRestriction_of_pointwise
#check @SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise_initialBoundaryLifting
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise_initialBoundaryLifting
#check @SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise
#check @SerrePositivity.KST.SConstruction.isPushoutSquare_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_of_pointwise
#check @SerrePositivity.KST.SConstruction.Ar
#print axioms SerrePositivity.KST.SConstruction.Ar
#check @SerrePositivity.KST.SConstruction.arObj
#print axioms SerrePositivity.KST.SConstruction.arObj
#check @SerrePositivity.KST.SConstruction.arMap
#print axioms SerrePositivity.KST.SConstruction.arMap
#check @SerrePositivity.KST.SConstruction.arMap_id
#print axioms SerrePositivity.KST.SConstruction.arMap_id
#check @SerrePositivity.KST.SConstruction.arMap_comp
#print axioms SerrePositivity.KST.SConstruction.arMap_comp
#check @SerrePositivity.KST.SConstruction.arNerve
#print axioms SerrePositivity.KST.SConstruction.arNerve
#check @SerrePositivity.KST.SConstruction.arNerveMap
#print axioms SerrePositivity.KST.SConstruction.arNerveMap
#check @SerrePositivity.KST.SConstruction.arNerveMap_id
#print axioms SerrePositivity.KST.SConstruction.arNerveMap_id
#check @SerrePositivity.KST.SConstruction.arNerveMap_comp
#print axioms SerrePositivity.KST.SConstruction.arNerveMap_comp
#check @SerrePositivity.KST.SConstruction.diagramSpace
#print axioms SerrePositivity.KST.SConstruction.diagramSpace
#check @SerrePositivity.KST.SConstruction.intervalStep
#print axioms SerrePositivity.KST.SConstruction.intervalStep
#check @SerrePositivity.KST.SConstruction.intervalStep_le
#print axioms SerrePositivity.KST.SConstruction.intervalStep_le
#check @SerrePositivity.KST.SConstruction.le_intervalStep
#print axioms SerrePositivity.KST.SConstruction.le_intervalStep
#check @SerrePositivity.KST.SConstruction.arSquareOrder
#print axioms SerrePositivity.KST.SConstruction.arSquareOrder
#check @SerrePositivity.KST.SConstruction.arSquare
#print axioms SerrePositivity.KST.SConstruction.arSquare
#check @SerrePositivity.KST.SConstruction.IsGapped
#print axioms SerrePositivity.KST.SConstruction.IsGapped
#check @SerrePositivity.KST.SConstruction.arSquare_naturality
#print axioms SerrePositivity.KST.SConstruction.arSquare_naturality
#check @SerrePositivity.KST.SConstruction.IsGapped.precomp
#print axioms SerrePositivity.KST.SConstruction.IsGapped.precomp
#check @SerrePositivity.KST.SConstruction.gappedSubcomplex
#print axioms SerrePositivity.KST.SConstruction.gappedSubcomplex
#check @SerrePositivity.KST.SConstruction.sConstruction
#print axioms SerrePositivity.KST.SConstruction.sConstruction
#check @SerrePositivity.KST.SConstruction.sConstruction_quasicategory
#print axioms SerrePositivity.KST.SConstruction.sConstruction_quasicategory
#check @SerrePositivity.KST.SConstruction.sMap
#print axioms SerrePositivity.KST.SConstruction.sMap
#check @SerrePositivity.KST.SConstruction.sMap_ι
#print axioms SerrePositivity.KST.SConstruction.sMap_ι
#check @SerrePositivity.KST.SConstruction.sMap_id
#print axioms SerrePositivity.KST.SConstruction.sMap_id
#check @SerrePositivity.KST.SConstruction.sMap_comp
#print axioms SerrePositivity.KST.SConstruction.sMap_comp
#check @SerrePositivity.KST.SConstruction.simplicialSConstruction
#print axioms SerrePositivity.KST.SConstruction.simplicialSConstruction
#check @SerrePositivity.KST.SConstruction.frameInclusion
#print axioms SerrePositivity.KST.SConstruction.frameInclusion
#check @SerrePositivity.KST.SConstruction.firstRowFrameMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameMap_inclusion
#check @SerrePositivity.KST.SConstruction.IsGapped.zeroFrameVertex
#print axioms SerrePositivity.KST.SConstruction.IsGapped.zeroFrameVertex
#check @SerrePositivity.KST.SConstruction.gappedFrameRestriction
#print axioms SerrePositivity.KST.SConstruction.gappedFrameRestriction
#check @SerrePositivity.KST.SConstruction.frameRowRestriction
#print axioms SerrePositivity.KST.SConstruction.frameRowRestriction
#check @SerrePositivity.KST.SConstruction.firstRowRestriction_factor
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_factor
#check @SerrePositivity.KST.SConstruction.frameRowDiagramIso
#print axioms SerrePositivity.KST.SConstruction.frameRowDiagramIso
#check @SerrePositivity.KST.SConstruction.frameRowRestriction_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.frameRowRestriction_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.initialBoundaryLifting_map_iso
#print axioms SerrePositivity.KST.SConstruction.initialBoundaryLifting_map_iso
#check @SerrePositivity.KST.SConstruction.internalHomFlipHomEquiv_evaluate
#print axioms SerrePositivity.KST.SConstruction.internalHomFlipHomEquiv_evaluate
#check @SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex.zero_evaluation
#print axioms SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex.zero_evaluation
#check @SerrePositivity.KST.SConstruction.cofiberFamilySquare
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySquare
#check @SerrePositivity.KST.SConstruction.cofiberFamilySquare_evaluate
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySquare_evaluate
#check @SerrePositivity.KST.SConstruction.cofiberFamilySquare_zero_corner
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySquare_zero_corner
#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle
#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_isCofiber
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_isCofiber
#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_apex
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_apex
#check @SerrePositivity.KST.SConstruction.IsPushoutDiagramVertex
#print axioms SerrePositivity.KST.SConstruction.IsPushoutDiagramVertex
#check @SerrePositivity.KST.SConstruction.pushoutDiagrams
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagrams
#check @SerrePositivity.KST.SConstruction.squareCoconeDiagramIso
#print axioms SerrePositivity.KST.SConstruction.squareCoconeDiagramIso
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso
#check @SerrePositivity.KST.SConstruction.pushoutProjection
#print axioms SerrePositivity.KST.SConstruction.pushoutProjection
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_projection
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_projection
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_inv_projection
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_inv_projection
#check @SerrePositivity.KST.SConstruction.exists_relative_pushoutFamily
#print axioms SerrePositivity.KST.SConstruction.exists_relative_pushoutFamily
#check @SerrePositivity.KST.SConstruction.pushoutProjection_hasLiftingProperty_boundary
#print axioms SerrePositivity.KST.SConstruction.pushoutProjection_hasLiftingProperty_boundary
#check @SerrePositivity.KST.SConstruction.exists_relative_colimitCoconeFamily
#print axioms SerrePositivity.KST.SConstruction.exists_relative_colimitCoconeFamily
#check @SerrePositivity.KST.SConstruction.colimitCoconeFamily_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.colimitCoconeFamily_relative_lifting
#check @SerrePositivity.KST.SConstruction.exists_lift_of_initial_first_vertices
#print axioms SerrePositivity.KST.SConstruction.exists_lift_of_initial_first_vertices
#check @SerrePositivity.KST.SConstruction.exists_extension_with_vertices
#print axioms SerrePositivity.KST.SConstruction.exists_extension_with_vertices
#check @SerrePositivity.KST.SConstruction.exists_extension_of_initial_or_terminal_endpoints
#print axioms SerrePositivity.KST.SConstruction.exists_extension_of_initial_or_terminal_endpoints
#check @SerrePositivity.KST.SConstruction.zeroChoices
#print axioms SerrePositivity.KST.SConstruction.zeroChoices
#check @SerrePositivity.KST.SConstruction.zeroChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.zeroChoices_isContractibleKan
#check @SerrePositivity.KST.SConstruction.zeroChoices_kanComplex
#print axioms SerrePositivity.KST.SConstruction.zeroChoices_kanComplex
#check @SerrePositivity.KST.SConstruction.exists_zeroChoices_extension
#print axioms SerrePositivity.KST.SConstruction.exists_zeroChoices_extension
#check @SerrePositivity.KST.SConstruction.IsDiagonal
#print axioms SerrePositivity.KST.SConstruction.IsDiagonal
#check @SerrePositivity.KST.SConstruction.IsPositiveRow
#print axioms SerrePositivity.KST.SConstruction.IsPositiveRow
#check @SerrePositivity.KST.SConstruction.positiveRow_orderConvex
#print axioms SerrePositivity.KST.SConstruction.positiveRow_orderConvex
#check @SerrePositivity.KST.SConstruction.positiveRow_of_frame_not_diagonal
#print axioms SerrePositivity.KST.SConstruction.positiveRow_of_frame_not_diagonal
#check @SerrePositivity.KST.SConstruction.frameChain_diagonal_endpoint
#print axioms SerrePositivity.KST.SConstruction.frameChain_diagonal_endpoint
#check @SerrePositivity.KST.SConstruction.FrameAr
#print axioms SerrePositivity.KST.SConstruction.FrameAr
#check @SerrePositivity.KST.SConstruction.frameForgetOrder
#print axioms SerrePositivity.KST.SConstruction.frameForgetOrder
#check @SerrePositivity.KST.SConstruction.frameNerve
#print axioms SerrePositivity.KST.SConstruction.frameNerve
#check @SerrePositivity.KST.SConstruction.framePositiveRow
#print axioms SerrePositivity.KST.SConstruction.framePositiveRow
#check @SerrePositivity.KST.SConstruction.frameNerve_diagonal_endpoint
#print axioms SerrePositivity.KST.SConstruction.frameNerve_diagonal_endpoint
#check @SerrePositivity.KST.SConstruction.zeroFrame_extend_boundary
#print axioms SerrePositivity.KST.SConstruction.zeroFrame_extend_boundary
#check @SerrePositivity.KST.SConstruction.IsZeroFrameVertex
#print axioms SerrePositivity.KST.SConstruction.IsZeroFrameVertex
#check @SerrePositivity.KST.SConstruction.zeroFrameDiagrams
#print axioms SerrePositivity.KST.SConstruction.zeroFrameDiagrams
#check @SerrePositivity.KST.SConstruction.zeroFrameProjection
#print axioms SerrePositivity.KST.SConstruction.zeroFrameProjection
#check @SerrePositivity.KST.SConstruction.diagonal_not_positiveRow
#print axioms SerrePositivity.KST.SConstruction.diagonal_not_positiveRow
#check @SerrePositivity.KST.SConstruction.diagonal_not_mem_framePositiveRow
#print axioms SerrePositivity.KST.SConstruction.diagonal_not_mem_framePositiveRow
#check @SerrePositivity.KST.SConstruction.exists_zeroFrame_extension
#print axioms SerrePositivity.KST.SConstruction.exists_zeroFrame_extension
#check @SerrePositivity.KST.SConstruction.zeroFrameProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.zeroFrameProjection_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.mk
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.mk
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.family
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.family
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.boundary
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.boundary
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.input
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.input
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.mk
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.mk
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame_boundary
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame_boundary
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.firstRow
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.firstRow
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.cofibers
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.cofibers

#check @SerrePositivity.KST.SConstruction.isInitialVertex_pointCoslice_of_isInvertibleEdge
#print axioms SerrePositivity.KST.SConstruction.isInitialVertex_pointCoslice_of_isInvertibleEdge

#check @SerrePositivity.KST.SConstruction.identityCocone
#print axioms SerrePositivity.KST.SConstruction.identityCocone

#check @SerrePositivity.KST.SConstruction.identityCocone_isColimit
#print axioms SerrePositivity.KST.SConstruction.identityCocone_isColimit

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_of_map_eq
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_of_map_eq

#check @SerrePositivity.KST.SConstruction.identityCocone_val
#print axioms SerrePositivity.KST.SConstruction.identityCocone_val

#check @SerrePositivity.KST.SConstruction.pointCocone_isColimit_of_constant
#print axioms SerrePositivity.KST.SConstruction.pointCocone_isColimit_of_constant

#check @SerrePositivity.KST.SConstruction.horn_one_one_eq_last_face
#print axioms SerrePositivity.KST.SConstruction.horn_one_one_eq_last_face

#check @SerrePositivity.KST.SConstruction.lastVertex_rightAnodyne
#print axioms SerrePositivity.KST.SConstruction.lastVertex_rightAnodyne

#check @SerrePositivity.KST.SConstruction.edgeTargetShape
#print axioms SerrePositivity.KST.SConstruction.edgeTargetShape

#check @SerrePositivity.KST.SConstruction.edgeTargetShape_inl
#print axioms SerrePositivity.KST.SConstruction.edgeTargetShape_inl

#check @SerrePositivity.KST.SConstruction.edgeTargetShape_restrict_last
#print axioms SerrePositivity.KST.SConstruction.edgeTargetShape_restrict_last

#check @SerrePositivity.KST.SConstruction.edgeTargetCocone
#print axioms SerrePositivity.KST.SConstruction.edgeTargetCocone

#check @SerrePositivity.KST.SConstruction.edgeTargetCocone_isColimit
#print axioms SerrePositivity.KST.SConstruction.edgeTargetCocone_isColimit

#check @SerrePositivity.KST.SConstruction.identityLegAttachment_isPushout
#print axioms SerrePositivity.KST.SConstruction.identityLegAttachment_isPushout

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_leg
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_leg

#check @SerrePositivity.KST.SConstruction.spanCoconeSquare_fst_restrict
#print axioms SerrePositivity.KST.SConstruction.spanCoconeSquare_fst_restrict

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_fst
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_fst

#check @SerrePositivity.KST.SConstruction.identityFirstLegAttachment_isPushout
#print axioms SerrePositivity.KST.SConstruction.identityFirstLegAttachment_isPushout

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_first_leg
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_first_leg

#check @SerrePositivity.KST.SConstruction.spanCoconeSquare_snd_restrict
#print axioms SerrePositivity.KST.SConstruction.spanCoconeSquare_snd_restrict

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_snd
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_snd

#check @SerrePositivity.KST.SConstruction.arCofiberSquareOrder_mem_frame
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareOrder_mem_frame

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareOrder
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareOrder

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_inclusion

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_firstRow
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_firstRow

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_diagonal
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_diagonal

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_isPushout
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_isPushout

#check @SerrePositivity.KST.SConstruction.frameCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamily

#check @SerrePositivity.KST.SConstruction.frameCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamily_vertex

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_zero_corner
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_zero_corner

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_ι
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_ι

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_apex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_apex

#check @SerrePositivity.KST.SConstruction.frameCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamily_apex

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_apex

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_vertex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_vertex

#check @SerrePositivity.KST.SConstruction.IsZeroFrameVertex.frameCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.IsZeroFrameVertex.frameCofiberFamily_vertex

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_ι
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_ι

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_apex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_apex

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_apex
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_apex

#check @SerrePositivity.KST.SConstruction.ihomCurry_pre_whiskerLeft
#print axioms SerrePositivity.KST.SConstruction.ihomCurry_pre_whiskerLeft

#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_frame
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_frame

#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_frame
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_frame

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_bottom
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_bottom

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_input
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_input

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_input
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_input

#check @SerrePositivity.KST.SConstruction.frameInclusion_mono
#print axioms SerrePositivity.KST.SConstruction.frameInclusion_mono

#check @SerrePositivity.KST.SConstruction.exists_arCofiberCompletion_preserving_frame
#print axioms SerrePositivity.KST.SConstruction.exists_arCofiberCompletion_preserving_frame

#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_frame
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_frame

#check @SerrePositivity.KST.SConstruction.exists_firstRowCofiberData_preserving_frame
#print axioms SerrePositivity.KST.SConstruction.exists_firstRowCofiberData_preserving_frame

#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_frame
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_frame

#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_firstRow
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_firstRow

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_of_vertexSurjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_boundary
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_boundary

#check @SerrePositivity.KST.SConstruction.intervalTriple
#print axioms SerrePositivity.KST.SConstruction.intervalTriple

#check @SerrePositivity.KST.SConstruction.arCofiberRectangleOrder
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangleOrder

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle_left

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle_outer
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle_outer

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle_right
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle_right

#check @SerrePositivity.KST.SConstruction.arSquares_isPushout_of_triples
#print axioms SerrePositivity.KST.SConstruction.arSquares_isPushout_of_triples

#check @SerrePositivity.KST.SConstruction.isGapped_iff_triples
#print axioms SerrePositivity.KST.SConstruction.isGapped_iff_triples

#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_zero_diagonal
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_zero_diagonal

#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_firstRow
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_firstRow

#check @SerrePositivity.KST.SConstruction.exists_firstRowDiagramWithZeroDiagonal
#print axioms SerrePositivity.KST.SConstruction.exists_firstRowDiagramWithZeroDiagonal

#check @SerrePositivity.KST.SConstruction.HasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.HasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.exists_pointwiseColimitCone
#print axioms SerrePositivity.KST.SConstruction.exists_pointwiseColimitCone

#check @SerrePositivity.KST.SConstruction.hasColimit_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.hasColimit_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.of_vertexIso
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.of_vertexIso

#check @SerrePositivity.KST.SConstruction.isPointwiseColimitCone_of_isColimitCone_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isPointwiseColimitCone_of_isColimitCone_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_pointwise_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_pointwise_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_iff_pointwise_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_iff_pointwise_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.reindexFunctorCocone
#print axioms SerrePositivity.KST.SConstruction.reindexFunctorCocone

#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.reindex
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.reindex

#check @SerrePositivity.KST.SConstruction.isColimitCone_reindex_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_reindex_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.fullSubcomplex_hasLiftingProperty_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.fullSubcomplex_hasLiftingProperty_of_vertexSurjective

#check @SerrePositivity.KST.SConstruction.isInitialVertex_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isInitialVertex_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.isTerminalVertex_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isTerminalVertex_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.isGapped_const
#print axioms SerrePositivity.KST.SConstruction.isGapped_const

#check @SerrePositivity.KST.SConstruction.sConstructionZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sConstructionZeroVertex

#check @SerrePositivity.KST.SConstruction.sConstructionZeroVertex_isZero
#print axioms SerrePositivity.KST.SConstruction.sConstructionZeroVertex_isZero

#check @SerrePositivity.KST.SConstruction.sMap_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.sMap_zeroVertex

#check @SerrePositivity.KST.SConstruction.sConstruction_hasZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sConstruction_hasZeroVertex

#check @SerrePositivity.KST.SConstruction.sConstructionZero_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sConstructionZero_isZeroVertex

#check @SerrePositivity.KST.SConstruction.sConstructionZero_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.sConstructionZero_isContractibleKan

#check @SerrePositivity.KST.SConstruction.sConstructionZero_kanComplex
#print axioms SerrePositivity.KST.SConstruction.sConstructionZero_kanComplex

#check @SerrePositivity.KST.SConstruction.firstRowZero_hom_ext
#print axioms SerrePositivity.KST.SConstruction.firstRowZero_hom_ext

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_zero_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_zero_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.arSquare_repeat_left
#print axioms SerrePositivity.KST.SConstruction.arSquare_repeat_left

#check @SerrePositivity.KST.SConstruction.arSquare_repeat_right
#print axioms SerrePositivity.KST.SConstruction.arSquare_repeat_right

#check @SerrePositivity.KST.SConstruction.arSquare_isPushout_of_repeated_endpoints
#print axioms SerrePositivity.KST.SConstruction.arSquare_isPushout_of_repeated_endpoints

#check @SerrePositivity.KST.SConstruction.isGapped_one_of_zero_diagonal
#print axioms SerrePositivity.KST.SConstruction.isGapped_one_of_zero_diagonal

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_trivialKanFibration_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_trivialKanFibration_of_vertexSurjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_one_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_one_vertex_surjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_one_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_one_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.arTwoMiddleSquare
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleSquare

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetractionOrder
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetractionOrder

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_order_comp
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_order_comp

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction

#check @SerrePositivity.KST.SConstruction.arTwoMiddleSquare_retraction
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleSquare_retraction

#check @SerrePositivity.KST.SConstruction.arTwoMiddleSquare_mono
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleSquare_mono

#check @SerrePositivity.KST.SConstruction.arTwoMiddle
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle

#check @SerrePositivity.KST.SConstruction.arTwoMiddleIso
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleIso

#check @SerrePositivity.KST.SConstruction.arTwoMiddleIso_ι
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleIso_ι

#check @SerrePositivity.KST.SConstruction.arTwo_obj_middle_or_endpoint
#print axioms SerrePositivity.KST.SConstruction.arTwo_obj_middle_or_endpoint

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_obj_back
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_obj_back

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_square
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_square

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_mem_of_vertices
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_mem_of_vertices

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_vertices_of_mem
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_vertices_of_mem

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_first
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_first

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_last
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_last

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_missing_endpoint
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_missing_endpoint

#check @SerrePositivity.KST.SConstruction.exists_arTwo_extension_with_zero_endpoints
#print axioms SerrePositivity.KST.SConstruction.exists_arTwo_extension_with_zero_endpoints

#check @SerrePositivity.KST.SConstruction.isGapped_two_of_cofiber_middle
#print axioms SerrePositivity.KST.SConstruction.isGapped_two_of_cofiber_middle

#check @SerrePositivity.KST.SConstruction.exists_gapped_arTwo_of_cofiber
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_arTwo_of_cofiber

#check @SerrePositivity.KST.SConstruction.firstRow_two_middle_bottom
#print axioms SerrePositivity.KST.SConstruction.firstRow_two_middle_bottom

#check @SerrePositivity.KST.SConstruction.exists_gapped_arTwo_with_firstRow
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_arTwo_with_firstRow

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_two_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_two_vertex_surjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_two_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_two_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting
#print axioms SerrePositivity.KST.SConstruction.relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting

#check @SerrePositivity.KST.SConstruction.sliceUnder_empty_hom_ext
#print axioms SerrePositivity.KST.SConstruction.sliceUnder_empty_hom_ext

#check @SerrePositivity.KST.SConstruction.cosliceEndpointMap_trivialKanFibration_of_initialBoundaryLifting
#print axioms SerrePositivity.KST.SConstruction.cosliceEndpointMap_trivialKanFibration_of_initialBoundaryLifting

#check @SerrePositivity.KST.SConstruction.exists_relativeInitialCosliceLift
#print axioms SerrePositivity.KST.SConstruction.exists_relativeInitialCosliceLift

#check @SerrePositivity.KST.SConstruction.stdSimplex_firstVertex_leftAnodyne
#print axioms SerrePositivity.KST.SConstruction.stdSimplex_firstVertex_leftAnodyne

#check @SerrePositivity.KST.SConstruction.pointCosliceVertexOfEdge_projection
#print axioms SerrePositivity.KST.SConstruction.pointCosliceVertexOfEdge_projection

#check @SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_invertibleEdge
#print axioms SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_invertibleEdge

#check @SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_vertexIso
#print axioms SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_vertexIso

#check @SerrePositivity.KST.SConstruction.IsColimitCone.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.IsColimitCone.of_functorIso

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_of_functorIso
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_of_functorIso

#check @SerrePositivity.KST.SConstruction.IsPushoutSquare.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.IsPushoutSquare.of_functorIso

#check @SerrePositivity.KST.SConstruction.exists_initialCoconeVertex_over_invertible_edge
#print axioms SerrePositivity.KST.SConstruction.exists_initialCoconeVertex_over_invertible_edge

#check @SerrePositivity.KST.SConstruction.HasColimit.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.HasColimit.of_functorIso

#check @SerrePositivity.KST.SConstruction.hasColimit_iff_of_functorIso
#print axioms SerrePositivity.KST.SConstruction.hasColimit_iff_of_functorIso
