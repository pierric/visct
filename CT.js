// Copyright 2011 David Galles, University of San Francisco. All rights reserved.
//
// Redistribution and use in source and binary forms, with or without modification, are
// permitted provided that the following conditions are met:
//
// 1. Redistributions of source code must retain the above copyright notice, this list of
// conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright notice, this list
// of conditions and the following disclaimer in the documentation and/or other materials
// provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY David Galles ``AS IS'' AND ANY EXPRESS OR IMPLIED
// WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
// FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> OR
// CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
// SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
// ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
// NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
// ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
// The views and conclusions contained in the software and documentation are those of the
// authors and should not be interpreted as representing official policies, either expressed
// or implied, of the University of San Francisco


// Constants.

CT.LINK_COLOR = "#007700";
CT.HIGHLIGHT_CIRCLE_COLOR = "#007700";
CT.FOREGROUND_COLOR = "#007700";
CT.BACKGROUND_COLOR = "#EEFFEE";

CT.WIDTH_DELTA  = 60;
CT.HEIGHT_DELTA = 60;
CT.STARTING_Y = 50;
CT.HOOKL_Y = 50;
CT.HOOKR_Y = 50;

function CT(am, w, h)
{
	this.init(am, w, h);
}

CT.prototype = new Algorithm();
CT.prototype.constructor = CT;
CT.superclass = Algorithm.prototype;

CT.prototype.init = function(am, w, h)
{
	var sc = CT.superclass;
	this.startingX =  w / 3;
	this.first_print_pos_y  = h - 2 * CT.PRINT_VERTICAL_GAP;
	this.print_max  = w - 10;
        this.treeRoot = hsLeaf();
        this.config = hsConfig(this.startingX, CT.STARTING_Y,
                               this.startingX+250,CT.HOOKL_Y,
                               this.startingX+450, CT.HOOKR_Y,
                               CT.WIDTH_DELTA, CT.HEIGHT_DELTA, 
                               CT.FOREGROUND_COLOR, CT.BACKGROUND_COLOR,
                               CT.LINK_COLOR,
                               CT.HIGHLIGHT_CIRCLE_COLOR, 
                               CT.HIGHLIGHT_CIRCLE_COLOR,
                               CT.HIGHLIGHT_CIRCLE_COLOR);
	var fn = sc.init;
	fn.call(this,am);
	this.addControls();
	this.nextIndex = 0;
	this.commands = [];
	this.cmd("CreateLabel", 0, "", 20, 10, 0);
	this.nextIndex = 1;
	this.animationManager.StartNewAnimation(this.commands);
	this.animationManager.skipForward();
	this.animationManager.clearHistory();
	
}

CT.prototype.addControls =  function()
{
	this.freeField = addControlToAlgorithmBar("Text", "");
	this.freeField.onkeydown = this.returnSubmit(this.freeField,  this.freeCallback.bind(this), 20);
	this.freeButton = addControlToAlgorithmBar("Button", "Free");
	this.freeButton.onclick = this.freeCallback.bind(this);
}

CT.prototype.reset = function()
{
	this.nextIndex = 1;
	this.treeRoot = hsLeaf();
}

CT.prototype.freeCallback = function(event)
{
	var insertedValue = this.freeField.value;
	// Get text value
	if (insertedValue != "")
	{
		// set text value
		this.freeField.value = "";
		this.implementAction(this.freeElement.bind(this), insertedValue);
	}
}

CT.prototype.freeElement = function(insertedValue)
{
	this.commands = new Array();	
	this.cmd("SetText", 0, "Inserting "+insertedValue);
	
    [r,n,c] = hsFree(hsPiece(insertedValue), this.treeRoot,
                     this.nextIndex, this.config);
    this.treeRoot  = r;
    this.nextIndex = n;
    hsCmds(this.commands, c);
    var log = document.getElementById("log");
    log.innerHTML = "";
    for (c in this.commands)
    {
        log.innerHTML += this.commands[c] + "<br/>";
    }

	this.cmd("SetText", 0, "");				
	return this.commands;
}

CT.prototype.disableUI = function(event)
{
	this.freeField.disabled = true;
	this.freeButton.disabled = true;
}

CT.prototype.enableUI = function(event)
{
	this.freeField.disabled = false;
	this.freeButton.disabled = false;
}

var currentAlg;

function init()
{
	var animManag = initCanvas();
	currentAlg = new CT(animManag, canvas.width, canvas.height);
}
