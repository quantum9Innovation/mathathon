$(document).ready(function(){

	$("#itemExport").click(function(e){
		var form = $.find('#itemList');
		if(!$.isBlank(form)) {
			var checkedLength = $('#itemList input[name=id]:checked').length;
			if(checkedLength == 0) {
				alert(ITEM_NO_SELECT);
				return;
			} else {
				$(this).target = "_blank";
				$.popupWindow("", {name:'exportPopup',height:750, width:700, scrollbars:true});

		    	$(form).prop("target","exportPopup");
		    	$(form).prop("action", context+"/srch/popup/srchExportPopup");
		    	$(form).submit();
			}
		}
	});

	$('.collecitonIpChk').unbind('click').bind('click',function(e){
		e.preventDefault();
		alert('등록된 IP가 아닙니다.');
	});


    //상세검색 팝업
    $('.detailSearch').click(function(e){
        e.preventDefault();
        $('.detailSrchPop').fadeIn();
    });
    $('.detailSrchPop .close').click(function(e){
        e.preventDefault();
        $('.detailSrchPop').fadeOut();
    });

    //검색 - 도움말 팝업
    $('.search .helpBtn').click(function(e){
        e.preventDefault();
        if($(this).hasClass('on')){
            $(this).removeClass('on');
            $('.srhHelpPop').fadeOut();
        }else{
            $(this).addClass('on');
            $('.srhHelpPop').fadeIn();
        }
    })

    $('.helpTab>li>a').click(function(e){
        e.preventDefault();
        $('.helpTab>li').removeClass('on')
        $(this).parent().addClass('on');
        $('.helpTabCont').removeClass('on');
        $('.helpTabCont').eq($(this).parent().index()).addClass('on')
    });

    //검색박스 인풋 패딩 조절
    let srhBtnWWidth = $('.searchBtnW').outerWidth(true) + 8;
    $('.search .searhArea input[type="text"]').css('padding-right',srhBtnWWidth)

    //atoz 슬라이드
 //    let atozTab = new Swiper('.atozTab .inner',{
	// 	slidesPerView:'auto',
	// 	spaceBetween: 0,
	// 	freeMode: true,
	// });

    //atoz tab
    $('.atozTab .item a').click(function(e){
//        e.preventDefault();
        $('.atozTab .item').removeClass('on')
        $(this).parent().addClass('on');
        $('.atozCont').removeClass('on');
        $('.atozCont').eq($(this).parent().index()).addClass('on');
        if(!$('.atozCont').eq($(this).parent().index()).children('.atozDepth2').length>0){
            $('.atozCont').eq($(this).parent().index()).find('.atozDepth3W').children().addClass('on');
        }
    });

	$(document).on("click", ".atozContTit", function(){

	    $('.atozCont .atozDepth2 .atozContTit').click(function(e){
	        e.preventDefault();
	        $(this).parents('.atozCont').find('.atozDepth2').removeClass('on');
	        $(this).parents('.atozCont').find('.atozDepth2>li').removeClass('on');
	        $(this).parents('.atozDepth2').addClass('on');
	        $(this).parent().addClass('on');
	        $(this).parents('.atozCont').find('.atozDepth3').removeClass('on');
	        $(this).parents('.atozCont').find('.atozDepth3W').children('.atozDepth3').eq($(this).parent().index()).addClass('on');

	    });

	});

    //검색상세 책이미지 체크
    if($('.bookDetailInfo .bookImg').length){
        $('.bookDetailInfo').addClass('img')
    }

    $('.bookContent .moreBtn').click(function(e){
        e.preventDefault();
        if($(this).hasClass('on')){
            $(this).removeClass('on').text('more');
            $(this).parents('.bookContent').find('.bcTxt').removeClass('on');
        }else{
            $(this).addClass('on').text('fold');;
            $(this).parents('.bookContent').find('.bcTxt').addClass('on');
        }
    });

    //권호정보 토글
    $('.searchResult .fBookTit').click(function(e){
        e.preventDefault();
        if($(this).parents('li').hasClass('on')){
            $(this).parents('li').removeClass('on');
            $(this).parents('li').find('ul').slideUp();
        }else{
            $(this).parents('li').addClass('on');
            $(this).parents('li').find('ul').slideDown();
        }
    });
    $('.searchResult .fBookList>li.on').children('ul').show();
});

function orgView(id){
/*	var userAgent = window.navigator.userAgent.toLowerCase();
	if(userAgent.indexOf("Microsoft Internet Explorer") > -1 || userAgent.indexOf("trident") > -1 || userAgent.indexOf("edge") > -1) {
		var link = document.createElement('a');
		link.href = context+"/common/orgView/"+id;
		link.target = 'orgView';
		document.body.appendChild(link);
		var popup = $.popupWindow('', {name:'orgView',height:750, width:700, scrollbars:true, resizable:true});
		link.click();
		return false;
	}
*/
	$(this).target = "_blank";
	var popup = $.popupWindow(context+"/common/orgView/"+id, {name:'orgView',height:900, width:850, scrollbars:true, resizable:true});
	popup.location.href = context+'/common/orgView/'+id;
};


function orgView2(id){
	$(this).target = "_blank";
	var popup = $.popupWindow(context+"/common/documentViewer/"+id, {name:'orgView',height:750, width:700, scrollbars:true, resizable:true});
	//popup.location.href = context+'/common/orgView/'+id; //두번호출
};

function orgMediaView(id){
	$(this).target = "_blank";
	var popup = $.popupWindow(context+"/common/mediaOrgView/"+id, {name:'orgView',height:750, width:700, scrollbars:true, resizable:true});
	//popup.location.href = context+'/common/orgView/'+id; //두번호출
};
